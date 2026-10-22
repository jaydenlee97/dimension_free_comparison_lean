#define _GNU_SOURCE
#include <unistd.h>
#include <dlfcn.h>
#include <stdio.h>
#include <string.h>
/* Runtime portability only: this host exposes /proc/self/exe but not
   /proc/<getpid()>/exe. Redirect only that process's own executable lookup. */
ssize_t readlink(const char *path, char *buf, size_t size) {
  static ssize_t (*original)(const char*, char*, size_t);
  if (!original) original = dlsym(RTLD_NEXT, "readlink");
  char own[64];
  snprintf(own, sizeof(own), "/proc/%d/exe", getpid());
  return original(strcmp(path, own) == 0 ? "/proc/self/exe" : path, buf, size);
}
