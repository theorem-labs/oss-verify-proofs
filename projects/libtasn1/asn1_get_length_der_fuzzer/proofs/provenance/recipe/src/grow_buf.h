                                                
  
                                                                              
                                                                          
                                                                             
                                                                         
                                                              
  
                                                                            
                                                                             
   
#ifndef GROW_BUF_H
#define GROW_BUF_H
#include <stdlib.h>
#include <string.h>

static inline void *grow_buf(void *old, size_t used, size_t newcap) {
  void *nb = malloc(newcap);
  if (!nb) return NULL;
  if (used) memcpy(nb, old, used);
  free(old);
  return nb;
}
#endif                 
