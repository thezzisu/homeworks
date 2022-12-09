/**
 * ZProxy - a tiny HTTP proxy
 * @file   parser.c
 * @author Zisu Zhang <2100012732@stu.pku.edu.cn>
 * MIT License
 */
#include "parser.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static const char *port_http = "80";
static const char *port_https = "443";
static const char *empty_path = "";

/**
 * z_parse_request_line: parse a request line
 */
void z_parse_request_line(char *line,
                          struct z_http_request_line *request_line) {
  printf("%s\n", line);
  char *saveptr;
  char *method = strtok_r(line, " ", &saveptr);
  char *uri = strtok_r(NULL, " ", &saveptr);
  char *version = strtok_r(NULL, "\r", &saveptr);
  request_line->method = strdup(method);
  request_line->uri = strdup(uri);
  request_line->version = strdup(version);
}

/**
 * z_free_request_line: free a request line
 */
void z_free_request_line(struct z_http_request_line request_line) {
  free(request_line.method);
  free(request_line.uri);
  free(request_line.version);
}

/**
 * z_parse_authority: parse an authority
 */
void z_parse_authority(char *authority, struct z_authority *parsed_authority) {
  char *saveptr;
  char *host = strtok_r(authority, ":", &saveptr);
  char *port = strtok_r(NULL, "", &saveptr);
  parsed_authority->host = strdup(host);
  if (port == NULL) {
    parsed_authority->port = strdup(port_http);
  } else {
    parsed_authority->port = strdup(port);
  }
}

/**
 * z_free_authority: free an authority
 */
void z_free_authority(struct z_authority parsed_authority) {
  free(parsed_authority.host);
  free(parsed_authority.port);
}

/**
 * z_parse_uri: parse a URI
 */
void z_parse_uri(char *uri, struct z_uri *parsed_uri) {
  char *saveptr;
  const char *scheme = strtok_r(uri, "://", &saveptr);
  char *authority = strdup(strtok_r(NULL, "/", &saveptr));
  const char *path = strtok_r(NULL, "", &saveptr);
  const char *host = strtok_r(authority, ":", &saveptr);
  const char *port = strtok_r(NULL, "", &saveptr);
  if (port == NULL) {
    if (strcmp(scheme, "https") == 0) {
      port = port_https;
    }
    port = port_http;
  }
  if (path == NULL) {
    path = empty_path;
  }
  parsed_uri->scheme = strdup(scheme);
  parsed_uri->host = strdup(host);
  parsed_uri->port = strdup(port);
  parsed_uri->path = strdup(path);
  free(authority);
}

/**
 * z_free_uri: free a URI
 */
void z_free_uri(struct z_uri parsed_uri) {
  free(parsed_uri.scheme);
  free(parsed_uri.host);
  free(parsed_uri.port);
  free(parsed_uri.path);
}

/**
 * z_parse_header: parse a header
 */
void z_parse_header(char *header, struct z_http_header *parsed_header) {
  char *saveptr;
  char *name = strtok_r(header, ":", &saveptr);
  char *value = strtok_r(NULL, "\r", &saveptr);
  parsed_header->name = strdup(name);
  parsed_header->value = strdup(value + 1);
}

/**
 * z_free_header: free a header
 */
void z_free_header(struct z_http_header parsed_header) {
  free(parsed_header.name);
  free(parsed_header.value);
}