                                                                                                   
  
                                                                                         
                                                                                                
                                                                                          
                                                                                              
                                                                                     
                                                                        
  
                                                                                            
                                                                                       
                                                                                              
                                                                                           
                                       
#ifndef OFT_REL_STR_H
#define OFT_REL_STR_H
#ifdef OFT_RELEASE_BUILD
#ifndef OFT_REL_STR
#define OFT_REL_STR(internal, release) release
#endif
#define OFT_REL_NOASAN __attribute__((no_sanitize("address")))
                                                                                            
                                                                                          
                                                                                         
                                                                                       
                                                                                     
                                                                                        
                                                                                             
                                                                               









                                                                                           
                                                                                              
                                                                   



#else
#ifndef OFT_REL_STR
#define OFT_REL_STR(internal, release) internal
#endif
#define OFT_REL_NOASAN
#endif
#endif                    
