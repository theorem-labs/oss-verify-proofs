                                                                  
  
                    
  
                                                                
  
                                                                         
  
                                                                         
                                        
  
                                                                             
                                                                  
                                                                             
                                                                             
                                                                            
                                                                               
                                                                            
                                                           
                                                              
                                                                         
                                                                
  
                                                                   
                                                                         
                                                                          
                                                                             
                                                                               
                                                                               
                                                                     
                                                                          
                                               
  
                                                                            
                                                                         
                                                                             
                                                        
                                                                 
  
                                                                                     
                                                                               
                                                                               
                                                                            
                                                                             
                                                                           
                                                        
  
                                                                            
                                                                               
                                                                              
                                                                            
                                                                            
                                                                          
                                                                               
                                                                               
                                                                          
                                                                              
                                                                              
                                                
  
                                                                    
                                                                         
                                                                             
                                                                               
                                                                     
                                                                              
                                                                              
                                                    
   
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "grow_buf.h"
#include "target.h"

                                                                               
  
                                                                                
                                                                                
                                                                                
                                                                            
                                                                                
                                                                                
                                                    
  
                                                                                
                                                                         
                                                                           
                                                                            
                                        
#define MAX_INPUT (64u << 20)

#define HDR_MIN 6                                             

                                                                    
                                                                    
#define CFG_LEN_MASK   0x7fffu
#define CFG_COUNT_BIT  0x8000u
                                                                              
                                                                         
                                                     
#define COUNT_MAX 251

#ifdef HARNESS_QUIET
#define DIAG(...) ((void)0)
#else
#define DIAG(...) fprintf(stderr, __VA_ARGS__)
#endif

                                                                                       
                                                                            
                                                                             
                                                                           
                                                                            
                                                                            
                                                                          
                                                                           
                                                                          
                                                                
  
                                                                                   
                                                                           
                                                                             
                                                                                
                                                                     
                                                                            
                      
const char *__asan_default_options(void);
const char *__asan_default_options(void) { return "allocator_may_return_null=1"; }

                                                                
                                                                    
                                                                            
                                                                            
                                                                           
                                                                         
                                                                   
                                                                        
                                                                       
                                                                           
                                                                             
                                                                       
                                                                      
                                                                            
                                                                           
static unsigned char read_stage[1u << 16];

static unsigned char *read_all(const char *path, size_t *out_len) {
  int fd = open(path, O_RDONLY);
  if (fd < 0) { DIAG("cli: cannot open %s\n", path); exit(2); }
  size_t cap = 1 << 16, len = 0;
  unsigned char *buf = (unsigned char *)malloc(cap);
  if (!buf) { DIAG("cli: out of memory\n"); exit(2); }
  for (;;) {
    if (len == cap) {
      if (cap >= MAX_INPUT) { DIAG("cli: input >= %u bytes, refused\n", MAX_INPUT); exit(2); }
      unsigned char *nb = (unsigned char *)grow_buf(buf, len, cap * 2);
      if (!nb) { DIAG("cli: out of memory\n"); exit(2); }
      buf = nb; cap *= 2;
    }
                                                        
                                                                       
                                                                  
                                                                       
                                                                          
                                                                             
                                                                             
                                                
                                                                        
                                                                           
                                                                        
                                                                          
                                                                            
                                                                        
                                                             
    size_t want = cap - len;
    if (want > sizeof read_stage) want = sizeof read_stage;
    ssize_t n = read(fd, read_stage, want);
    if (n < 0) { DIAG("cli: read error on %s\n", path); exit(2); }
    if (n == 0) break;
    memcpy(buf + len, read_stage, (size_t)n);
    len += (size_t)n;
  }
  close(fd);
  *out_len = len;
  return buf;
}

int main(int argc, char **argv) {
  if (argc != 2) { DIAG("usage: %s INPUT\n", argv[0]); return 2; }

  size_t len = 0;
  unsigned char *buf = read_all(argv[1], &len);
  if (len < HDR_MIN) { DIAG("cli: input shorter than header\n"); free(buf); return 2; }

  unsigned cfg_word = (unsigned)buf[0] | ((unsigned)buf[1] << 8);
  int count_allocs = (cfg_word & CFG_COUNT_BIT) != 0;
  size_t config_len = (size_t)(cfg_word & CFG_LEN_MASK);
  if (len < HDR_MIN + config_len) { DIAG("cli: config_len overruns input\n"); free(buf); return 2; }

  const unsigned char *config = buf + 2;
  const unsigned char *p = config + config_len;
  unsigned int bitmap = (unsigned int)p[0] | ((unsigned int)p[1] << 8) |
                        ((unsigned int)p[2] << 16) | ((unsigned int)p[3] << 24);
  const unsigned char *payload = p + 4;
  size_t payload_len = len - HDR_MIN - config_len;

  target_alloc_init(bitmap);
  int status = target_run(config, config_len, payload, payload_len);

                                                                             
                                                                    
  if (count_allocs) {
    unsigned n = target_alloc_count();
    status = n < COUNT_MAX ? (int)n : COUNT_MAX;
  }

  free(buf);
  return status;
}
