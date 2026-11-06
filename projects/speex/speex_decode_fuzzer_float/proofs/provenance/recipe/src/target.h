                                                          
  
                                                                         
                                                                               
   
#ifndef TARGET_H
#define TARGET_H
#include <stddef.h>

                                                           
const char *target_name(void);

                                                                           
                                                                                
                                                                        
                                                                              
                                                                          
                                                                         
                                                                          
                                                                           
                                                                            
                                                                             
                                                                             
               
  
                                                                              
                                                                  
                                                                      
                                                                              
                              
void target_alloc_init(unsigned int fail_bitmap);

                                                                            
                                                                             
                                                                         
                                                                         
                                                                   
  
                                                                             
                                                                               
                                                               
unsigned target_alloc_count(void);

                                                                              
                                                                  
  
                                                                          
                                                                              
int target_run(const unsigned char *config, size_t config_len,
               const unsigned char *payload, size_t payload_len);
#endif               
