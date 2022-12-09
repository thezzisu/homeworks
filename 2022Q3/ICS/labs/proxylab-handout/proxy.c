/**
 * ZProxy - a tiny HTTP proxy
 * @file   proxy.c
 * @author Zisu Zhang <2100012732@stu.pku.edu.cn>
 * MIT License
 */
#include <pthread.h>
#include <stdio.h>
#include <string.h>
#include <sys/select.h>
#include <sys/socket.h>
#include <sys/types.h>

#include "cache.h"
#include "csapp.h"
#include "parser.h"

/* Recommended max cache and object sizes */
#define MAX_CACHE_SIZE 1049000
#define MAX_OBJECT_SIZE 102400

/* You won't lose style points for including this long line in your code */
static const char *user_agent_hdr =
    "User-Agent: Mozilla/5.0 (X11; Linux x86_64; rv:10.0.3) Gecko/20120305 "
    "Firefox/10.0.3\r\n";

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wdiscarded-qualifiers"
/**
 * rio_writes: wrapper for rio_writen, which writes a string to a fd
 */
ssize_t rio_writes(int fd, const char *str) {
  return rio_writen(fd, str, strlen(str));
}
#pragma GCC diagnostic pop

static struct zp_cache *cache;

/**
 * handle_connect: handle HTTP CONNECT requests
 */
void *handle_connect(int fd, rio_t *rp, char *buffer,
                     struct z_http_request_line request_line) {
  struct z_authority authority;
  z_parse_authority(request_line.uri, &authority);
  for (;;) {
    // Simple ignore all the headers
    rio_readlineb(rp, buffer, MAXLINE);
    if (buffer[0] == '\r') {
      break;
    }
  }
  int client_fd = open_clientfd(authority.host, authority.port);
  if (client_fd < 0) {
    rio_writes(fd, "HTTP/1.0 500 Internal Server Error\r\n");
    rio_writes(fd, "\r\n");
    rio_writes(fd, "500 Internal Server Error\r\n");
    z_free_authority(authority);
    z_free_request_line(request_line);
    free(buffer);
    free(rp);
    close(fd);
    return NULL;
  }
  z_free_authority(authority);
  z_free_request_line(request_line);
  free(rp);
  rio_writes(fd, "HTTP/1.0 200 Connection Established\r\n");
  rio_writes(fd, "Connection: close\r\n");
  rio_writes(fd, "\r\n");
  fd_set read_set;
  int max_fd = fd > client_fd ? fd : client_fd;
  for (;;) {
    FD_ZERO(&read_set);
    FD_SET(fd, &read_set);
    FD_SET(client_fd, &read_set);
    select(max_fd + 1, &read_set, NULL, NULL, NULL);
    if (FD_ISSET(fd, &read_set)) {
      ssize_t n = read(fd, buffer, MAXLINE);
      if (n <= 0) {
        break;
      }
      rio_writen(client_fd, buffer, n);
    }
    if (FD_ISSET(client_fd, &read_set)) {
      ssize_t n = read(client_fd, buffer, MAXLINE);
      if (n <= 0) {
        break;
      }
      rio_writen(fd, buffer, n);
    }
  }
  free(buffer);
  close(fd);
  return NULL;
}

/**
 * handle_client: Handle a client request
 */
void *handle_client(void *args) {
  int fd = (int)(size_t)args;
  rio_t *rp = (rio_t *)malloc(sizeof(rio_t));
  rio_readinitb(rp, fd);
  char *buffer = (char *)malloc(MAXLINE);
  ssize_t line_len = rio_readlineb(rp, buffer, MAXLINE);
  if (line_len >= MAXLINE - 1) {
    rio_writes(fd, "HTTP/1.0 400 Bad Request\r\n");
    rio_writes(fd, "\r\n");
    rio_writes(fd, "400 Bad Request\r\n");
    free(buffer);
    free(rp);
    close(fd);
    return NULL;
  }
  struct z_http_request_line request_line;
  z_parse_request_line(buffer, &request_line);
#ifdef DEBUG
  printf("Method: %s, URI: %s, Version: %s\n", request_line.method,
         request_line.uri, request_line.version);
#endif
  if (strcmp(request_line.method, "CONNECT") == 0) {
    return handle_connect(fd, rp, buffer, request_line);
  }
  size_t cache_len;
  char *cached_buf = zp_cache_get(cache, request_line.uri, &cache_len);
  if (cached_buf) {
#ifdef DEBUG
    printf("Cache hit: %s\n", request_line.uri);
#endif
    rio_writen(fd, cached_buf, cache_len);
    free(cached_buf);
    z_free_request_line(request_line);
    free(buffer);
    free(rp);
    close(fd);
    return NULL;
  }
#ifdef DEBUG
  else {
    printf("Cache miss: %s\n", request_line.uri);
  }
#endif
  char *uri_copy = strdup(request_line.uri);
  struct z_uri parsed_uri;
  z_parse_uri(uri_copy, &parsed_uri);
  free(uri_copy);
  int client_fd = open_clientfd(parsed_uri.host, parsed_uri.port);
  if (client_fd < 0) {
    rio_writes(fd, "HTTP/1.0 500 Internal Server Error\r\n");
    rio_writes(fd, "\r\n");
    rio_writes(fd, "500 Internal Server Error\r\n");
    z_free_uri(parsed_uri);
    z_free_request_line(request_line);
    close(client_fd);
    free(buffer);
    free(rp);
    close(fd);
    return NULL;
  }
  rio_writes(client_fd, request_line.method);
  rio_writes(client_fd, " /");
  rio_writes(client_fd, parsed_uri.path);
  rio_writes(client_fd, " ");
  rio_writes(client_fd, "HTTP/1.0\r\n");
  uint8_t header_sent = 0;
  for (;;) {
    line_len = rio_readlineb(rp, buffer, MAXLINE);
    if (line_len == MAXLINE) {
      rio_writes(fd, "HTTP/1.0 400 Bad Request\r\n");
      rio_writes(fd, "\r\n");
      rio_writes(fd, "400 Bad Request\r\n");
      z_free_uri(parsed_uri);
      z_free_request_line(request_line);
      close(client_fd);
      free(buffer);
      free(rp);
      close(fd);
      return NULL;
    }
    if (buffer[0] == '\r') {
      break;
    }
    struct z_http_header header;
    z_parse_header(buffer, &header);
    if (strcasecmp(header.name, "User-Agent") == 0) {
      z_free_header(header);
      continue;
    }
    if (strcasecmp(header.name, "Connection") == 0) {
      z_free_header(header);
      continue;
    }
    if (strcasecmp(header.name, "Proxy-Connection") == 0) {
      z_free_header(header);
      continue;
    }
    if (strcasecmp(header.name, "Host") == 0) {
      header_sent = 1;
    }
    // Forward the header to the server
    rio_writes(client_fd, header.name);
    rio_writes(client_fd, ": ");
    rio_writes(client_fd, header.value);
    rio_writes(client_fd, "\r\n");
    z_free_header(header);
  }
  if (!header_sent) {
    rio_writes(client_fd, "Host: ");
    rio_writes(client_fd, parsed_uri.host);
    if (strcmp(parsed_uri.port, "80") != 0) {
      rio_writes(client_fd, ":");
      rio_writes(client_fd, parsed_uri.port);
    }
    rio_writes(client_fd, "\r\n");
  }
  rio_writes(client_fd, user_agent_hdr);
  rio_writes(client_fd, "Connection: close\r\n");
  rio_writes(client_fd, "Proxy-Connection: close\r\n");
  rio_writes(client_fd, "\r\n");
  // Read the response from the server
  char *cache_buf = (char *)malloc(MAX_OBJECT_SIZE);
  size_t cache_size = 0, cache_fit = 1;
  for (;;) {
    ssize_t n = rio_readn(client_fd, buffer, MAXLINE);
    if (n <= 0) break;
    rio_writen(fd, buffer, n);
    if (cache_size + n < MAX_OBJECT_SIZE) {
      memcpy(cache_buf + cache_size, buffer, n);
      cache_size += n;
    } else {
      cache_fit = 0;
    }
  }
  if (cache_fit) {
    zp_cache_put(cache, request_line.uri, cache_buf, cache_size);
  }
  free(cache_buf);
  z_free_uri(parsed_uri);
  z_free_request_line(request_line);
  close(client_fd);
  free(buffer);
  free(rp);
  close(fd);
  return NULL;
}

int main(int argc, char *argv[]) {
  // get a port number from the command line arguments
  if (argc != 2) {
    fprintf(stderr, "Usage: %s <port number>", argv[0]);
    exit(1);
  }
  int listen_fd = open_listenfd(argv[1]);
  if (listen_fd < 0) {
    fprintf(stderr, "open_listenfd error: %s", strerror(errno));
    return -1;
  }
  printf("Listening on port %s\n", argv[1]);
  printf("%s\n", user_agent_hdr);
  Signal(SIGPIPE, SIG_IGN);
  cache = malloc(sizeof(struct zp_cache));
  zp_cache_init(cache, MAX_CACHE_SIZE);
  while (1) {
#ifdef DEBUG
    struct sockaddr_in client_addr;
    socklen_t client_len = sizeof(client_addr);
    int conn_fd =
        accept(listen_fd, (struct sockaddr *)&client_addr, &client_len);
#else
    int conn_fd = accept(listen_fd, NULL, NULL);
#endif
    if (conn_fd < 0) {
      fprintf(stderr, "accept error: %s", strerror(errno));
      continue;
    }
#ifdef DEBUG
    char client_ip[INET_ADDRSTRLEN];
    inet_ntop(AF_INET, &client_addr.sin_addr, client_ip, INET_ADDRSTRLEN);
    printf("Client IP: %s, Port: %d\n", client_ip, client_addr.sin_port);
#endif

    pthread_t thread;
    Pthread_create(&thread, NULL, handle_client, (void *)(size_t)conn_fd);
  }
  return 0;
}
