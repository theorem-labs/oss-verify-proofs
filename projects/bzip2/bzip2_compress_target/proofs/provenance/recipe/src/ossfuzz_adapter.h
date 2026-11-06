                                                                  
  
                                                                 
                                                                            
                                                                              
                                                     
  
                                             
  
                                                               
  
                  
  
                                                                   
  
                                                                            
                                                                            
                                                                            
                                                                             
                                                                
  
                                                                                
                                                                             
                                                                            
                                                                              
                                                                             
                                                                              
                                                                    
  
                                                                   
  
                                                                             
                                                   
  
                                                                           
  
                                                                          
                                                                             
                                                                               
                                                                          
                                                                          
                                                                              
                                                                           
                                                                          
                                                                              
                                                                       
  
                                                                              
                                                                             
                                                                             
                                                                           
                                                                     
                                                                          
                                                                                
                                                                          
                                                                     
                                                                            
                                                                             
  
                                                                            
                                                                             
                                                                          
                                                                              
                                                                           
                                                                             
                                                                              
                                                                             
                                                                   
                                                                            
                                                                        
                                                                            
                                                                         
                                                                    
                                                                       
                                                                             
                                                                            
                                                                        
                                                                             
                                                                           
                                                   
  
                                                                      
                                                                             
                                                                              
                                                                           
                                                                           
                                                               
  
                                                                        
                                                                            
                                                                               
                                                                           
                                                                       
                                                                             
                                                       
                                                                        
                                                                          
                                                                             
                                 
                                                                     
                                                                            
                                                                              
                
                                                                             
                                                                               
                                                                            
                                   
  
                                                                          
                                                      
                                                                    
                                                                             
                                                                
  
                                                         
                                                                             
                                                                               
                                                                             
                                                                              
                                                                               
                                                                            
                                                           
  
                                                            
                                                                         
                                                                  
                                                                           
                                                                              
                                                                           
                                                             
  
                                                                             
                                           
  
                                                                               
                                                                          
                                                                              
                                                                             
                                                       
  
                                                                              
                                                                              
                                                                            
                                                                                 
                                                                             
                                                                              
               
  
                                                                              
                                            
  
                                                                         
                                                                           
                                                                       
                                                                              
                                                                           
                                                 
   
#ifndef OFT_OSSFUZZ_ADAPTER_H
#define OFT_OSSFUZZ_ADAPTER_H

#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "emit.h"
#include "target.h"

#ifndef OFT_TARGET_NAME
#error "define OFT_TARGET_NAME before including ossfuzz_adapter.h"
#endif

                                                                           
                                                                             
                                                  
int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size);

                                                                          
                                                                      
                                                                   
__attribute__((weak)) int LLVMFuzzerInitialize(int *argc, char ***argv);

const char *target_name(void) { return OFT_TARGET_NAME; }

                                
  
                                                                          
                                                                             
                                                                           
                                                                              
                                                                            
                                                                        
                                                                             
                                                                              
                                                                
  
                                                                           
                                                                          
                                                                   
  
                                                                               
                                                                               
                                                                         
                                                                              
                                                                             
                                                                              
                      
  
                                                                         
                                                                          
                                                                    
void target_alloc_init(unsigned int fail_bitmap) { (void)fail_bitmap; }
unsigned target_alloc_count(void) { return 0; }

                                                                               
                                                
static char oft_arg0[] = "fuzz";
static char *oft_argv[2] = {oft_arg0, NULL};
static int oft_argc = 1;

                                                                  
  
                                                                           
                                                                               
                                                                     
                                                   
  
                                                                          
  
                                                                               
                                                                     
  
                                                                              
                                                                            
                     
  
                                                                       
                                                               
  
                                                                            
                                                                              
                                                                                
                                                                                
                                                                                
                                                                       
  
                                                                              
                                                                              
                                                                                 
                                                                                
  
                                                                              
                                                                               
                                                              
  
                                                                            
                                                                                 
                                                                     
   
static const unsigned char *oft_aligned_copy(const unsigned char *payload,
                                             size_t payload_len, void **owned) {
  *owned = NULL;
  if (payload_len == 0) {
                                                                                
                                                                              
                                                                              
    static max_align_t empty;
    return (const unsigned char *)&empty;
  }
                                                                           
                                                         
  void *p = malloc(payload_len);
  if (p == NULL) return NULL;
  memcpy(p, payload, payload_len);
  *owned = p;
  return (const unsigned char *)p;
}

                                                                             
                                                                             
                                                                         
                                                              
                                                                              
                                                                         
                                                                         
                                                                          
                                                                       
                  
#define OFT_HARNESS_EXITED 77
#define OFT_HARNESS_BAD_RETURN 78

                                                                      
static int oft_in_callback = 0;

                                                                              
                                                                             
                                                                           
                                                                            
                                                                           
                                                                  
                                             
static void oft_exit_guard(void) {
  if (!oft_in_callback) return;
  fflush(stdout);
  _exit(OFT_HARNESS_EXITED);
}

int target_run(const unsigned char *config, size_t config_len,
               const unsigned char *payload, size_t payload_len) {
  static int initialized = 0;
  if (!initialized) {
    initialized = 1;
                                                                              
                                                                          
                                                                            
                                                                           
                                                                              
                                                                         
                                                                    
                                                           
    if (atexit(oft_exit_guard) != 0) return 2;
    if (LLVMFuzzerInitialize) {
      char **argv = oft_argv;
      LLVMFuzzerInitialize(&oft_argc, &argv);
    }
  }

  unsigned char c = config_len ? config[0] : 0;
  int calls = 1 + (c & 3);

  void *owned = NULL;
  const unsigned char *aligned = oft_aligned_copy(payload, payload_len, &owned);
  if (aligned == NULL) return 2;                                                      

  int rc = 0, bad_return = 0;
  for (int i = 0; i < calls; i++) {
    oft_in_callback = 1;
    rc = LLVMFuzzerTestOneInput((const uint8_t *)aligned, payload_len);
    oft_in_callback = 0;
                                                                               
                                                                                 
    emit_printf("%d\n", rc);
                                                                                
                                                                           
                                            
    if (rc != 0 && rc != -1) bad_return = 1;
  }

  free(owned);
  return bad_return ? OFT_HARNESS_BAD_RETURN : 0;
}

#endif                            
#include "rel_str.h"                                                                      
