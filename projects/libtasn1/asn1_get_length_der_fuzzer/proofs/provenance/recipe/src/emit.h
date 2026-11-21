                                                                            
                     
  
                                                                              
                                                                           
                                                                               
                                                                        
                                                                          
                                                                             
                                                                              
                                                                              
                                     
  
                                                                      
                                                                             
                                                                     
                                                                         
                                                                           
                                                                        
                                                                             
                                               
  
                                                                              
                                                                              
                                                                               
                                                                     
   
                                                                                
                                                                                
                                                                             
                                                                                 
                                                                            
#ifndef HARNESS_EMIT_H
#define HARNESS_EMIT_H

#include <stdarg.h>
#include <stddef.h>
#include <stdio.h>

#ifdef HARNESS_QUIET

                                                                             
                                                                          
                                                                             
                                                                          
                                                               
static inline int emit_printf(const char *fmt, ...) { (void)fmt; return 0; }
static inline size_t emit_bytes(const void *p, size_t n) { (void)p; return n; }
static inline int emit_putc(int c) { return c; }

#else

static inline int emit_printf(const char *fmt, ...) {
  va_list ap;
  int r;
  va_start(ap, fmt);
  r = vprintf(fmt, ap);
  va_end(ap);
  return r;
}
static inline size_t emit_bytes(const void *p, size_t n) {
  return fwrite(p, 1, n, stdout);
}
static inline int emit_putc(int c) { return putchar(c); }

#endif

#endif                     
