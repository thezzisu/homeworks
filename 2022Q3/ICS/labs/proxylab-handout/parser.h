/**
 * ZProxy - a tiny HTTP proxy
 * @file   parser.h
 * @author Zisu Zhang <2100012732@stu.pku.edu.cn>
 * MIT License
 */
#ifndef Z_PARSER
#define Z_PARSER

struct z_http_request_line {
  char *method;
  char *uri;
  char *version;
};

void z_parse_request_line(char *line, struct z_http_request_line *request_line);
void z_free_request_line(struct z_http_request_line request_line);

struct z_authority {
  char *host;
  char *port;
};

void z_parse_authority(char *authority, struct z_authority *parsed_authority);
void z_free_authority(struct z_authority parsed_authority);

struct z_uri {
  char *scheme;
  char *host;
  char *port;
  char *path;
};

void z_parse_uri(char *uri, struct z_uri *parsed_uri);
void z_free_uri(struct z_uri parsed_uri);

struct z_http_header {
  char *name;
  char *value;
};

void z_parse_header(char *header, struct z_http_header *parsed_header);
void z_free_header(struct z_http_header parsed_header);
#endif