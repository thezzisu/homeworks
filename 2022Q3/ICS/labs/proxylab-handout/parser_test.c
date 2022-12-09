#include "parser.h"

#include <stdio.h>
#include <string.h>

int main() {
  struct z_http_request_line request_line;
  char line[512];
  strcpy(line, "GET http://www.cmu.edu/hub/index.html HTTP/1.1");
  z_parse_request_line(line, &request_line);
  printf("Method: %s, URI: %s, Version: %s\n", request_line.method,
         request_line.uri, request_line.version);

  struct z_uri parsed_uri;
  z_parse_uri(request_line.uri, &parsed_uri);
  printf("Scheme: %s, Host: %s, Port: %s, Path: %s\n", parsed_uri.scheme,
         parsed_uri.host, parsed_uri.port, parsed_uri.path);

  strcpy(line, "Host: www.cmu.edu");
  struct z_http_header parsed_header;
  z_parse_header(line, &parsed_header);
  printf("Name: %s, Value: %s\n", parsed_header.name, parsed_header.value);
}