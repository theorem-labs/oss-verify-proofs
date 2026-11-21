(* NOT FOR STAGING. GENERATED, NOT WRITTEN BY HAND: THE LAYOUT TEXT OF ONE IMAGE, THE LIST FORM.
   Made by gen_layout_from_sbase_s1_e2.py from the image's base text of today, md5 ,
   and from the image's hand entry text, md5 (the entry's inner join point).
   It holds DATA only: numerals, names, lists. No lemma, no tactic. *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Import RunCtx.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require Import Base.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require Import ZArr ZArr4 ZRd IDefs IMem ITac ISpecs IGlue.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require Import SQuant SLayoutSigL.
Import ListNotations.
Open Scope Z_scope.

Module L.
  Definition L_INFLATE : Z := 86600.
  Definition L_DISP : Z := 86964.
  Definition L_DISP10 : Z := 86960.
  Definition L_SETMODE : Z := 86956.
  Definition L_DISP0 : Z := 86972.
  Definition L_LEAVE : Z := 93624.
  Definition L_LEAVE_LD : Z := 93620.
  Definition L_RET : Z := 94020.
  Definition L_NEED_DICT : Z := 94156.
  Definition L_MEM : Z := 93928.
  Definition L_RELOAD_A1 : Z := 91724.
  Definition L_RELOAD_RA : Z := 91728.
  Definition L_RELOAD : Z := 91732.
  Definition L_BADMSG_S11 : Z := 91752.
  Definition L_BADMSG_S10 : Z := 93024.
  Definition L_BADMSG_A3 : Z := 92872.
  Definition L_LEAVE_A4 : Z := 93484.
  Definition L_HEAD : Z := 87008.
  Definition L_DICTID : Z := 87200.
  Definition L_DICT : Z := 87760.
  Definition L_TYPE : Z := 87832.
  Definition L_TYPEDO : Z := 87848.
  Definition L_STORED : Z := 87280.
  Definition L_COPY_ : Z := 88028.
  Definition L_COPY : Z := 88036.
  Definition L_TABLE : Z := 87364.
  Definition L_LENLENS : Z := 87652.
  Definition L_CODELENS : Z := 87184.
  Definition L_LEN_ : Z := 91800.
  Definition L_LEN : Z := 91808.
  Definition L_LENEXT : Z := 87112.
  Definition L_DIST : Z := 92396.
  Definition L_DISTEXT : Z := 87192.
  Definition L_MATCH : Z := 92968.
  Definition L_LIT : Z := 87084.
  Definition L_CHECK : Z := 87576.
  Definition L_LENGTH : Z := 87668.
  Definition L_DONE : Z := 94180.
  Definition L_UW : Z := 94212.
  Definition L_UW_CALL : Z := 93900.
  Definition L_UW_RET : Z := 93904.
  Definition T_ZW : Z := 94288.
  Definition L_ZB : Z := 94292.
  Definition L_ITABLE : Z := 95716.
  Definition L_IFAST : Z := 99212.
  Definition ROMHI_S : Z := 135168.
  Definition FR_INF : Z := 224.
  Definition FR_UW : Z := 48.
  Definition FR_IT : Z := 192.
  Definition FR_IF : Z := 112.
  Definition FR_AD : Z := 32.
  Definition L_ENTRY_J : Z := 86800.
  Definition s_regs_entry_j : list (positive * quant) :=
    [ (kSP, Q_u_at (-224));
      (kGP, Q_entry kGP);
      (kTP, Q_entry kTP);
      (kS0, Q_p);
      (kA0, Q_u);
      (kA1, Q_lit 0);
      (kA2, Q_mode);
      (kA3, Q_lit 7160);
      (kA4, Q_lit 16384);
      (kS4, Q_lit 16209);
      (kS3, Q_next_out);
      (kS11, Q_next_in) ].
  Definition s_fix : list (positive * quant) :=
    [ (kSP, Q_u_at (-224));
      (kGP, Q_entry kGP);
      (kTP, Q_entry kTP);
      (kS0, Q_p);
      (kA0, Q_u);
      (kA1, Q_lit 0);
      (kS6, Q_p_at 168);
      (kT6, Q_lit (-16180));
      (kT4, Q_lit 30);
      (kS9, Q_lit JTAB_ADDR);
      (kS4, Q_lit 16209) ].
  Definition s_vars : list (positive * quant) :=
    [ (kS2, Q_avail_in);
      (kS3, Q_next_out);
      (kRA, Q_avail_out);
      (kS7, Q_hold);
      (kS8, Q_bits) ].
  Definition s_regs_leave : list (positive * quant) :=
    [ (kSP, Q_u_at (-224));
      (kGP, Q_entry kGP);
      (kTP, Q_entry kTP);
      (kS0, Q_p);
      (kA0, Q_u);
      (kA1, Q_lit 0);
      (kS11, Q_next_in);
      (kS2, Q_avail_in);
      (kS3, Q_next_out);
      (kRA, Q_avail_out);
      (kS7, Q_hold);
      (kS8, Q_bits);
      (kS1, Q_par) ].
  Definition s_regs_leave_ld : list (positive * quant) :=
    [ (kSP, Q_u_at (-224));
      (kGP, Q_entry kGP);
      (kTP, Q_entry kTP);
      (kS0, Q_p);
      (kA0, Q_u);
      (kA1, Q_lit 0);
      (kS11, Q_next_in);
      (kS2, Q_avail_in);
      (kS3, Q_next_out);
      (kRA, Q_avail_out);
      (kS7, Q_hold);
      (kS8, Q_bits) ].
  Definition s_regs_ret : list (positive * quant) :=
    [ (kSP, Q_u_at (-224));
      (kGP, Q_entry kGP);
      (kTP, Q_entry kTP);
      (kS5, Q_par) ].
  Definition s_regs_entry : list (positive * quant) :=
    [ (kSP, Q_u);
      (kA0, Q_u);
      (kA1, Q_lit 0);
      (kRA, Q_entry kRA);
      (kGP, Q_entry kGP);
      (kTP, Q_entry kTP);
      (kS0, Q_entry kS0);
      (kS1, Q_entry kS1);
      (kS2, Q_entry kS2);
      (kS3, Q_entry kS3);
      (kS4, Q_entry kS4);
      (kS5, Q_entry kS5);
      (kS6, Q_entry kS6);
      (kS7, Q_entry kS7);
      (kS8, Q_entry kS8);
      (kS9, Q_entry kS9);
      (kS10, Q_entry kS10);
      (kS11, Q_entry kS11) ].
  Definition s_regs_disp : list (positive * quant) :=
    [ (kS10, Q_next_in) ].
  Definition s_regs_d10 : list (positive * quant) :=
    [ (kS11, Q_next_in) ].
  Definition s_regs_d0 : list (positive * quant) :=
    [ (kS11, Q_next_in);
      (kA2, Q_mode) ].
  Definition s_regs_arm : list (positive * quant) :=
    [ (kS11, Q_next_in) ].
  Definition s_regs_reload_a1 : list (positive * quant) :=
    [ (kSP, Q_u_at (-224));
      (kGP, Q_entry kGP);
      (kTP, Q_entry kTP);
      (kS0, Q_p);
      (kA0, Q_u);
      (kS4, Q_lit 16209);
      (kS6, Q_p_at 168);
      (kS9, Q_lit JTAB_ADDR);
      (kS10, Q_next_in);
      (kS2, Q_avail_in);
      (kS3, Q_next_out);
      (kS1, Q_avail_out);
      (kS7, Q_hold);
      (kS8, Q_bits) ].
  Definition s_regs_reload_ra : list (positive * quant) :=
    [ (kSP, Q_u_at (-224));
      (kGP, Q_entry kGP);
      (kTP, Q_entry kTP);
      (kS0, Q_p);
      (kA0, Q_u);
      (kA1, Q_lit 0);
      (kS4, Q_lit 16209);
      (kS6, Q_p_at 168);
      (kS9, Q_lit JTAB_ADDR);
      (kS10, Q_next_in);
      (kS2, Q_avail_in);
      (kS3, Q_next_out);
      (kS1, Q_avail_out);
      (kS7, Q_hold);
      (kS8, Q_bits) ].
  Definition s_regs_reload : list (positive * quant) :=
    [ (kSP, Q_u_at (-224));
      (kGP, Q_entry kGP);
      (kTP, Q_entry kTP);
      (kS0, Q_p);
      (kA0, Q_u);
      (kA1, Q_lit 0);
      (kS4, Q_lit 16209);
      (kS6, Q_p_at 168);
      (kS9, Q_lit JTAB_ADDR);
      (kS10, Q_next_in);
      (kS2, Q_avail_in);
      (kS3, Q_next_out);
      (kRA, Q_avail_out);
      (kS7, Q_hold);
      (kS8, Q_bits) ].
  Definition s_regs_badmsg_s11 : list (positive * quant) :=
    [ (kA2, Q_par) ].
  Definition s_regs_badmsg_s10 : list (positive * quant) :=
    [ (kA2, Q_par) ].
  Definition s_regs_badmsg_a3 : list (positive * quant) :=
    [ (kS10, Q_next_in);
      (kA2, Q_avail_in);
      (kS3, Q_next_out);
      (kRA, Q_avail_out);
      (kS7, Q_hold);
      (kS8, Q_bits);
      (kA3, Q_par) ].
  Definition i_frame : list fslot :=
    [ ("entry_kRA"%string, (-8), W8, Q_entry kRA);
      ("entry_kS0"%string, (-16), W8, Q_entry kS0);
      ("entry_kS1"%string, (-24), W8, Q_entry kS1);
      ("entry_kS2"%string, (-32), W8, Q_entry kS2);
      ("entry_kS3"%string, (-40), W8, Q_entry kS3);
      ("entry_kS4"%string, (-48), W8, Q_entry kS4);
      ("entry_kS5"%string, (-56), W8, Q_entry kS5);
      ("entry_kS6"%string, (-64), W8, Q_entry kS6);
      ("entry_kS7"%string, (-72), W8, Q_entry kS7);
      ("entry_kS8"%string, (-80), W8, Q_entry kS8);
      ("entry_kS9"%string, (-88), W8, Q_entry kS9);
      ("entry_kS10"%string, (-96), W8, Q_entry kS10);
      ("entry_kS11"%string, (-104), W8, Q_entry kS11);
      ("lit_0"%string, (-120), W8, Q_lit 0);
      ("u"%string, (-128), W8, Q_u);
      ("lit_m16180"%string, (-136), W8, Q_lit (-16180));
      ("lit_16209"%string, (-152), W8, Q_lit 16209);
      ("avail_in0"%string, (-168), W8, Q_avail_in0);
      ("p_at_7160"%string, (-176), W8, Q_p_at 7160);
      ("lit_m5"%string, (-184), W8, Q_lit (-5));
      ("p_at_160"%string, (-192), W8, Q_p_at 160);
      ("p_at_808"%string, (-200), W8, Q_p_at 808);
      ("p_at_1384"%string, (-208), W8, Q_p_at 1384);
      ("p_at_136"%string, (-216), W8, Q_p_at 136);
      ("p_at_140"%string, (-224), W8, Q_p_at 140) ].
  Definition s_ret : list fslot :=
    [ ("ret"%string, (-160), W8, Q_ret) ].
  Definition s_out : list fslot :=
    [ ("out"%string, (-144), W8, Q_out) ].
  (* ---- PATCH: S_Stored.patch-P-r1.tsv md5 : 11 fields ---- *)
  Definition L_STORED_LOOP : Z := 87308.
  Definition L_STORED_BODY : Z := 87968.
  Definition L_STORED_BAD : Z := 89272.
  Definition L_COPY_MEMCPY : Z := 88080.
  Definition L_COPY_DONE : Z := 88156.
  Definition L_MEMCPY_RET : Z := 88108.
  Definition s_regs_copy_memcpy : list (positive * quant) :=
    [ (kSP, Q_u_at (-224));
      (kGP, Q_entry kGP);
      (kTP, Q_entry kTP);
      (kS0, Q_p);
      (kA0, Q_u);
      (kA1, Q_lit 0);
      (kS6, Q_p_at 168);
      (kS9, Q_lit JTAB_ADDR);
      (kS2, Q_avail_in);
      (kS3, Q_next_out);
      (kRA, Q_avail_out);
      (kS11, Q_next_in);
      (kS7, Q_hold);
      (kS8, Q_bits);
      (kS4, Q_par) ].
  Definition s_regs_stored_loop : list (positive * quant) :=
    [ (kS0, Q_p);
      (kS8, Q_bits);
      (kA3, Q_bits);
      (kA4, Q_next_in);
      (kS11, Q_next_in);
      (kS2, Q_avail_in);
      (kS7, Q_hold) ].
  Definition s_regs_stored_lv : list (positive * quant) :=
    [ (kA4, Q_next_in);
      (kS2, Q_avail_in);
      (kS7, Q_hold);
      (kS8, Q_bits) ].
  Definition s_regs_stored_dn : list (positive * quant) :=
    [ (kS11, Q_next_in);
      (kS2, Q_avail_in);
      (kS7, Q_hold);
      (kS8, Q_bits) ].
  Definition keep_stored_loop : list positive :=
    [ kSP; kGP; kTP; kS0; kA0; kA1; kS1; kRA; kS3; kS4; kS6; kT4; kS9; kT6 ].
  (* ---- PATCH: S_Check.patch-P-r1.tsv md5 : 12 fields ---- *)
  Definition L_DICT_CALL : Z := 87772.
  Definition L_ADLER_RET1 : Z := 87796.
  Definition L_CHECK_LOOP : Z := 87596.
  Definition L_CHECK_BODY : Z := 89596.
  Definition L_CHECK_CMP : Z := 90676.
  Definition s_regs_check_dict : list (positive * quant) :=
    [ (kSP, Q_u_at (-224));
      (kGP, Q_entry kGP);
      (kTP, Q_entry kTP);
      (kS0, Q_p);
      (kA0, Q_u);
      (kS4, Q_lit 16209);
      (kS6, Q_p_at 168);
      (kS9, Q_lit JTAB_ADDR);
      (kS2, Q_avail_in);
      (kS3, Q_next_out);
      (kRA, Q_avail_out);
      (kS7, Q_hold);
      (kS8, Q_bits);
      (kS11, Q_next_in) ].
  Definition s_regs_check_body : list (positive * quant) :=
    [ (kSP, Q_u_at (-224));
      (kGP, Q_entry kGP);
      (kTP, Q_entry kTP);
      (kS0, Q_p);
      (kA0, Q_u);
      (kA1, Q_lit 0);
      (kS6, Q_p_at 168);
      (kT6, Q_lit (-16180));
      (kT4, Q_lit 30);
      (kS9, Q_lit JTAB_ADDR);
      (kS4, Q_lit 16209);
      (kA3, Q_lit 5);
      (kS2, Q_avail_in);
      (kS3, Q_next_out);
      (kRA, Q_avail_out);
      (kS11, Q_next_in);
      (kS10, Q_next_in);
      (kS7, Q_hold);
      (kS8, Q_bits) ].
  Definition s_regs_check_cmp : list (positive * quant) :=
    [ (kSP, Q_u_at (-224));
      (kGP, Q_entry kGP);
      (kTP, Q_entry kTP);
      (kS0, Q_p);
      (kA0, Q_u);
      (kA1, Q_lit 0);
      (kS6, Q_p_at 168);
      (kT6, Q_lit (-16180));
      (kT4, Q_lit 30);
      (kS9, Q_lit JTAB_ADDR);
      (kS4, Q_lit 16209);
      (kA3, Q_lit 5);
      (kA4, Q_lit 4);
      (kS2, Q_avail_in);
      (kS3, Q_next_out);
      (kRA, Q_avail_out);
      (kS11, Q_next_in);
      (kS10, Q_next_in);
      (kS7, Q_hold);
      (kS8, Q_bits) ].
  Definition s_regs_check_loop : list (positive * quant) :=
    [ (kS0, Q_p);
      (kS8, Q_bits);
      (kA4, Q_bits);
      (kS11, Q_next_in);
      (kS2, Q_avail_in);
      (kS7, Q_hold) ].
  Definition s_regs_check_lv : list (positive * quant) :=
    [ (kS11, Q_next_in);
      (kS2, Q_avail_in);
      (kS7, Q_hold);
      (kS8, Q_bits) ].
  Definition s_regs_check_dn : list (positive * quant) :=
    [ (kS11, Q_next_in);
      (kS10, Q_next_in);
      (kS2, Q_avail_in);
      (kS7, Q_hold);
      (kS8, Q_bits) ].
  Definition keep_check_loop : list positive :=
    [ kSP; kGP; kTP; kS0; kA0; kA1; kA3; kS1; kRA; kS3; kS4; kS6; kT4; kS9; kT6 ].
  (* ---- PATCH: S_ZB.patch-P-r1.tsv md5 : 2 fields ---- *)
  Definition s_regs_zb : list (positive * quant) :=
    [ (kSP, Q_u_at (-272));
      (kA0, Q_par);
      (kS0, Q_next_out);
      (kS2, Q_lit 1);
      (kS3, Q_p);
      (kS5, Q_avail_in0);
      (kS6, Q_avail_out);
      (kS7, Q_hold);
      (kS8, Q_bits);
      (kS9, Q_out);
      (kS11, Q_next_in);
      (kGP, Q_entry kGP);
      (kTP, Q_entry kTP) ].
  Definition s_regs_zb_n : list (positive * quant) :=
    [ (kS1, Q_par);
      (kS4, Q_par) ].
  (* ---- PATCH: S_Type.patch-P-r1.tsv md5 : 3 fields ---- *)
  Definition L_TYPEDO_LAST : Z := 86940.
  Definition L_TYPEDO_BODY : Z := 87904.
  Definition L_TYPEDO_DROP : Z := 89460.
  (* ---- PATCH: S_ZAw-rows.tsv md5 : 26 fields ---- *)
  Definition L_UW_BODY : Z := 94300.
  Definition L_UW_EPI : Z := 94468.
  Definition L_UW_TAIL : Z := 94504.
  Definition L_UW_FULL : Z := 94436.
  Definition L_UW_PART : Z := 94312.
  Definition L_ZAW_PART_J : Z := 94332.
  Definition L_ZA : Z := 86352.
  Definition L_CALL2 : Z := 85648.
  Definition RA_II : Z := 85536.
  Definition A_MEMSET : Z := 132460.
  Definition s_regs_zaw_epi : list (positive * quant) :=
    [ (kSP, Q_arg_at 0 (-48));
      (kS2, Q_arg 1) ].
  Definition s_regs_zaw_ret : list (positive * quant) :=
    [ (kSP, Q_arg 0);
      (kA0, Q_arg 1);
      (kS0, Q_arg 2);
      (kS1, Q_arg 3);
      (kS2, Q_arg 4);
      (kS3, Q_arg 5);
      (kS4, Q_arg 6) ].
  Definition s_regs_zaw_tail : list (positive * quant) :=
    [ (kS3, Q_arg 0);
      (kS4, Q_arg 1);
      (kSP, Q_arg_at 2 (-48)) ].
  Definition s_regs_zaw_tail_k : list (positive * quant) :=
    [ (kS3, Q_arg 0);
      (kS4, Q_arg 1);
      (kSP, Q_arg_at 2 (-48));
      (kS2, Q_lit 0) ].
  Definition s_regs_zaw_fp : list (positive * quant) :=
    [ (kA0, Q_arg 0);
      (kA1, Q_lit 32768);
      (kS0, Q_arg 1);
      (kS1, Q_arg 2);
      (kS3, Q_arg 3);
      (kSP, Q_arg_at 4 (-48)) ].
  Definition s_regs_zaw_part_j : list (positive * quant) :=
    [ (kA0, Q_arg 0);
      (kA2, Q_arg 1);
      (kS0, Q_arg 2);
      (kS1, Q_arg 3);
      (kS3, Q_arg 4);
      (kSP, Q_arg_at 5 (-48));
      (kS2, Q_arg 6);
      (kS4, Q_arg 7) ].
  Definition s_regs_zaw_body : list (positive * quant) :=
    [ (kA0, Q_arg 0);
      (kS0, Q_arg 1);
      (kS1, Q_arg 2);
      (kS3, Q_arg 3);
      (kSP, Q_arg_at 4 (-48)) ].
  Definition s_regs_zaw_entry : list (positive * quant) :=
    [ (kA0, Q_arg 0);
      (kA1, Q_arg 1);
      (kA2, Q_arg 2);
      (kSP, Q_arg 3);
      (kRA, Q_arg 4);
      (kS0, Q_arg 5);
      (kS1, Q_arg 6);
      (kS2, Q_arg 7);
      (kS3, Q_arg 8);
      (kS4, Q_arg 9) ].
  Definition s_regs_zaw_kw : list (positive * quant) :=
    [ (kA3, Q_arg 0);
      (kA0, Q_lit 0);
      (kA1, Q_lit 32768);
      (kA2, Q_lit 1);
      (kS0, Q_arg 1);
      (kS1, Q_arg 2);
      (kS2, Q_lit 1);
      (kS3, Q_arg 3);
      (kS4, Q_arg 4);
      (kSP, Q_arg_at 5 (-48)) ].
  Definition s_regs_zaw_resume : list (positive * quant) :=
    [ (kA0, Q_arg 0);
      (kS0, Q_arg 1);
      (kS1, Q_arg 2);
      (kS2, Q_lit 1);
      (kS3, Q_arg 3);
      (kSP, Q_arg_at 4 (-48)) ].
  Definition s_regs_zaw_za : list (positive * quant) :=
    [ (kSP, Q_arg_at 0 (-32));
      (kS1, Q_arg 0);
      (kA0, Q_arg 1);
      (kS3, Q_arg 2);
      (kS4, Q_lit 262144);
      (kGP, Q_arg 3);
      (kTP, Q_arg 4);
      (kS5, Q_arg 5);
      (kS6, Q_arg 6);
      (kS7, Q_arg 7);
      (kS8, Q_arg 8);
      (kS9, Q_arg 9);
      (kS10, Q_arg 10);
      (kS11, Q_arg 11) ].
  Definition s_regs_zaw_za_k : list (positive * quant) :=
    [ (kSP, Q_arg 0);
      (kS0, Q_arg_at 0 168);
      (kS1, Q_arg_at 0 160);
      (kS2, Q_lit 4294967295);
      (kS3, Q_lit 0);
      (kS4, Q_lit 0);
      (kS5, Q_arg 5);
      (kGP, Q_arg 3);
      (kTP, Q_arg 4);
      (kS6, Q_arg 6);
      (kS7, Q_arg 7);
      (kS8, Q_arg 8);
      (kS9, Q_arg 9);
      (kS10, Q_arg 10);
      (kS11, Q_arg 11) ].
  Definition keep_zaw : list positive :=
    [ kGP; kTP; kS5; kS6; kS7; kS8; kS9; kS10; kS11 ].
  Definition keep_zaw_tail : list positive :=
    [ kS0; kS1; kGP; kTP; kS5; kS6; kS7; kS8; kS9; kS10; kS11 ].
  Definition f_zaw_uw : list fslot :=
    [ ("zaw_ra"%string, (-8), W8, Q_arg 0);
      ("zaw_s0"%string, (-16), W8, Q_arg 1);
      ("zaw_s1"%string, (-24), W8, Q_arg 2);
      ("zaw_s2"%string, (-32), W8, Q_arg 3);
      ("zaw_s3"%string, (-40), W8, Q_arg 4);
      ("zaw_s4"%string, (-48), W8, Q_arg 5) ].
  Definition f_zaw_ii : list fslot :=
    [ ("zaw_ii_a"%string, (-32), W8, Q_arg 1);
      ("zaw_ii_b"%string, (-24), W8, Q_arg_at 0 160);
      ("zaw_ii_c"%string, (-16), W8, Q_arg_at 0 168);
      ("zaw_ii_ra"%string, (-8), W8, Q_arg 2) ].
  (* ---- PATCH: S_ZBIback.patch-P-r3.tsv md5 : 23 fields ---- *)
  Definition L_ZBIB_SWITCH : Z := 96644.
  Definition L_ZBIB_INIT : Z := 96800.
  Definition L_ZBIB_LOOP : Z := 96852.
  Definition L_ZBIB_BRK : Z := 97308.
  Definition L_ZBIB_J80 : Z := 97340.
  Definition L_ZBIB_SETBITS : Z := 97360.
  Definition L_ZBIB_EPI : Z := 97368.
  Definition L_ZBIB_MAX0 : Z := 97468.
  Definition s_regs_zbib_init : list (positive * quant) :=
    [ (kT0, Q_arg 0);
      (kT1, Q_arg 1);
      (kA7, Q_arg 2);
      (kA0, Q_arg 3);
      (kT3, Q_arg 4);
      (kT2, Q_arg 5) ].
  Definition s_regs_zbib_switch : list (positive * quant) :=
    [ (kT0, Q_arg 0);
      (kT1, Q_arg 1);
      (kA7, Q_arg 2) ].
  Definition s_regs_zbib_rv : list (positive * quant) :=
    [ (kA6, Q_arg 0) ].
  Definition s_regs_zbib_brk : list (positive * quant) :=
    [ (kS8, Q_arg 0) ].
  Definition s_regs_zbib_j80 : list (positive * quant) :=
    [ (kT5, Q_arg 0) ].
  Definition s_regs_zbib_setbits : list (positive * quant) :=
    [ (kA4, Q_arg 0);
      (kA7, Q_arg 1) ].
  Definition s_regs_zbib_p3 : list (positive * quant) :=
    [ (kSP, Q_arg_at 0 (-192));
      (kGP, Q_arg 1);
      (kTP, Q_arg 2) ].
  Definition s_regs_zbib_out : list (positive * quant) :=
    [ (kA0, Q_arg 0);
      (kSP, Q_arg 1);
      (kRA, Q_arg 2);
      (kS0, Q_arg 3);
      (kS1, Q_arg 4);
      (kS2, Q_arg 5);
      (kS3, Q_arg 6);
      (kS4, Q_arg 7);
      (kS5, Q_arg 8);
      (kS6, Q_arg 9);
      (kS7, Q_arg 10);
      (kS8, Q_arg 11);
      (kS9, Q_arg 12);
      (kS10, Q_arg 13);
      (kS11, Q_arg 14);
      (kGP, Q_arg 15);
      (kTP, Q_arg 16) ].
  Definition s_regs_zbib_entry : list (positive * quant) :=
    [ (kGP, Q_arg 0);
      (kTP, Q_arg 1);
      (kS0, Q_arg 2);
      (kS1, Q_arg 3);
      (kS2, Q_arg 4);
      (kS3, Q_arg 5);
      (kS4, Q_arg 6);
      (kS5, Q_arg 7);
      (kS6, Q_arg 8);
      (kS7, Q_arg 9);
      (kS8, Q_arg 10);
      (kS9, Q_arg 11);
      (kS10, Q_arg 12);
      (kS11, Q_arg 13) ].
  Definition f_zbib_slots : list fslot :=
    [ ("ra"%string, (-8), W8, Q_arg 0);
      ("s0"%string, (-16), W8, Q_arg 1);
      ("s1"%string, (-24), W8, Q_arg 2);
      ("s2"%string, (-32), W8, Q_arg 3);
      ("s3"%string, (-40), W8, Q_arg 4);
      ("s4"%string, (-48), W8, Q_arg 5);
      ("s5"%string, (-56), W8, Q_arg 6);
      ("s6"%string, (-64), W8, Q_arg 7);
      ("s7"%string, (-72), W8, Q_arg 8);
      ("s8"%string, (-80), W8, Q_arg 9);
      ("s9"%string, (-88), W8, Q_arg 10);
      ("s10"%string, (-96), W8, Q_arg 11);
      ("s11"%string, (-104), W8, Q_arg 12) ].
  Definition FR_ZBIB_CNT : Z := (-136).
  Definition FR_ZBIB_CNT_END : Z := (-104).
  Definition FR_ZBIB_FLAGS : Z := (-184).
  Definition FR_ZBIB_FLAGS_END : Z := (-168).
  Definition FR_ZBIB_LOCALS : Z := 88.
  (* ---- PATCH: S_ZAw-rows-b.tsv md5 : 5 fields ---- *)
  Definition FR_ZAW_STACK_LO : Z := (-1024).
  Definition FR_ZAW_STACK_LEN : Z := 1232.
  Definition FR_ZAW_STACK_TOP : Z := 208.
  Definition FR_ZAW_BELOW_LO : Z := (-80).
  Definition FR_ZAW_BELOW_LEN : Z := 48.
  (* ---- PATCH: S_ZBF-rows.tsv md5 : 37 fields ---- *)
  Definition L_FENTRY : Z := 99212.
  Definition L_FHEAD : Z := 99444.
  Definition L_FLOOK : Z := 99484.
  Definition L_FLIT : Z := 99588.
  Definition L_FLATCH : Z := 99604.
  Definition L_FLENB : Z := 99616.
  Definition L_FDLOOK : Z := 99716.
  Definition L_FDISTB : Z := 99816.
  Definition L_FWIN : Z := 99916.
  Definition L_FDIRECT : Z := 100044.
  Definition L_FFROMOUT : Z := 100256.
  Definition L_FCOPY3 : Z := 100260.
  Definition L_FCOPY3B : Z := 100268.
  Definition L_FFROMWIN : Z := 100356.
  Definition L_FEOB : Z := 100388.
  Definition L_FBADD : Z := 100420.
  Definition L_FMSG : Z := 100428.
  Definition L_FEXIT : Z := 100444.
  Definition L_FTOOFAR : Z := 100572.
  Definition L_FC3TA : Z := 100316.
  Definition L_FC3T1 : Z := 100320.
  Definition L_FWLOOP2 : Z := 100012.
  Definition L_FDLOOP : Z := 100056.
  Definition L_FDTAIL : Z := 100096.
  Definition L_FLENJ : Z := 99676.
  Definition L_FLENJ2 : Z := 99652.
  Definition L_FDISTJ : Z := 99880.
  Definition L_FWL_WR : Z := 99976.
  Definition L_FWL_WR_X : Z := 100000.
  Definition L_FWL_W0 : Z := 100168.
  Definition L_FWL_W0_X : Z := 100192.
  Definition L_FWL_CT : Z := 100228.
  Definition L_FWL_CT_X : Z := 100252.
  Definition L_FWLOOP2_X : Z := 100036.
  Definition L_FW0 : Z := 100144.
  Definition L_FCONTIG : Z := 100204.
  Definition L_FWRAP : Z := 99944.
  (* ---- PATCH: S_ZA-rows.tsv md5 : 19 fields ---- *)
  Definition L_LCHECK : Z := 93732.
  Definition L_LDT : Z := 93796.
  Definition L_UW_ARGS : Z := 93888.
  Definition L_LNOWIN : Z := 93936.
  Definition L_LRC : Z := 93972.
  Definition L_ZA_LFIN : Z := 94008.
  Definition L_EXIT : Z := 85676.
  Definition T_ZE1 : Z := 94664.
  Definition T_ZE2 : Z := 94688.
  Definition RA2 : Z := 85728.
  Definition L_TAIL : Z := 85664.
  Definition L_C1 : Z := 85580.
  Definition L_C2 : Z := 85648.
  Definition RA_C1 : Z := 85592.
  Definition RA_C2 : Z := 85660.
  Definition s_regs_za_fin : list (positive * quant) :=
    [ (kSP, Q_u_at (-224));
      (kGP, Q_entry kGP);
      (kTP, Q_entry kTP);
      (kA0, Q_arg 0);
      (kS1, Q_arg 1) ].
  Definition s_regs_za_uwret : list (positive * quant) :=
    [ (kSP, Q_u_at (-224));
      (kGP, Q_entry kGP);
      (kTP, Q_entry kTP);
      (kA0, Q_arg 0);
      (kS1, Q_arg 1);
      (kS5, Q_avail_in0);
      (kS2, Q_avail_in);
      (kS9, Q_out);
      (kS3, Q_avail_out);
      (kS0, Q_p) ].
  Definition s_regs_za_kw : list (positive * quant) :=
    [ (kA3, Q_lit A_ZCALLOC);
      (kA0, Q_lit 0);
      (kA1, Q_lit WIN_SIZE);
      (kA2, Q_lit 1);
      (kS0, Q_next_out);
      (kS1, Q_arg 1);
      (kS2, Q_lit 1);
      (kS3, Q_p);
      (kS4, Q_arg 1);
      (kSP, Q_u_at (-272));
      (kGP, Q_entry kGP);
      (kTP, Q_entry kTP);
      (kS5, Q_avail_in0);
      (kS6, Q_avail_out);
      (kS7, Q_hold);
      (kS8, Q_bits);
      (kS9, Q_out);
      (kS11, Q_next_in) ].
  Definition f_za_kw : list fslot :=
    [ ("ra"%string, (-232), W8, Q_lit L_UW_RET);
      ("s0"%string, (-240), W8, Q_p);
      ("s1"%string, (-248), W8, Q_arg 0);
      ("s2"%string, (-256), W8, Q_avail_in);
      ("s3"%string, (-264), W8, Q_avail_out);
      ("s4"%string, (-272), W8, Q_arg 1) ].
  (* ---- PATCH: S_ZB-rows.tsv md5 : 3 fields ---- *)
  Definition s_regs_zb_v : list (positive * quant) :=
    [ (kSP, Q_u_at (-272));
      (kA0, Q_arg 2);
      (kS0, Q_next_out);
      (kS1, Q_arg 0);
      (kS2, Q_lit 1);
      (kS3, Q_p);
      (kS4, Q_arg 0);
      (kS5, Q_avail_in0);
      (kS6, Q_avail_out);
      (kS7, Q_hold);
      (kS8, Q_bits);
      (kS9, Q_out);
      (kS11, Q_next_in);
      (kGP, Q_entry kGP);
      (kTP, Q_entry kTP) ].
  Definition f_zb_tok : list fslot :=
    [ ("t1"%string, (-232), W8, Q_lit L_UW_RET);
      ("t2"%string, (-240), W8, Q_p);
      ("t3"%string, (-248), W8, Q_arg 1);
      ("t4"%string, (-256), W8, Q_avail_in);
      ("t5"%string, (-264), W8, Q_avail_out);
      ("t6"%string, (-272), W8, Q_arg 0) ].
  Definition s_regs_zb_tok : list (positive * quant) :=
    [ (kS0, Q_next_out);
      (kS1, Q_arg 0);
      (kS2, Q_lit 1);
      (kS3, Q_p);
      (kS4, Q_arg 0);
      (kS5, Q_avail_in0);
      (kS6, Q_avail_out);
      (kS7, Q_hold);
      (kS8, Q_bits);
      (kS9, Q_out);
      (kS10, Q_arg 2);
      (kS11, Q_next_in) ].
  (* ---- PATCH: S_ZBFBack-rows.tsv md5 : 22 fields ---- *)
  Definition s_regs_zbf_cregs : list (positive * quant) :=
    [ (kA1, Q_arg 0);
      (kA3, Q_arg 1);
      (kA7, Q_arg 2);
      (kS11, Q_arg 3) ].
  Definition s_regs_zbf_kl : list (positive * quant) :=
    [ (kA4, Q_arg 0) ].
  Definition s_regs_zbf_wloop : list (positive * quant) :=
    [ (kT2, Q_arg 0);
      (kS10, Q_arg 1);
      (kRA, Q_arg 2);
      (kA4, Q_arg 3);
      (kS9, Q_arg 4) ].
  Definition s_regs_zbf_wloop_k : list (positive * quant) :=
    [ (kT2, Q_arg 0);
      (kS10, Q_arg 1);
      (kRA, Q_arg 2);
      (kA4, Q_arg 3) ].
  Definition s_regs_zbf_wloop2 : list (positive * quant) :=
    [ (kS10, Q_arg 0);
      (kT2, Q_arg 1);
      (kA4, Q_arg 2) ].
  Definition s_regs_zbf_c3loop : list (positive * quant) :=
    [ (kRA, Q_arg 0);
      (kA4, Q_arg 1);
      (kS10, Q_arg 2) ].
  Definition s_regs_zbf_c3loop_k : list (positive * quant) :=
    [ (kRA, Q_arg 0);
      (kS9, Q_arg 1);
      (kA4, Q_arg 2);
      (kT2, Q_arg 3);
      (kS10, Q_arg 4) ].
  Definition s_regs_zbf_c3tail : list (positive * quant) :=
    [ (kS9, Q_arg 0);
      (kT2, Q_arg 1);
      (kS10, Q_arg 2) ].
  Definition s_regs_zbf_copy3w : list (positive * quant) :=
    [ (kRA, Q_arg 0);
      (kA4, Q_arg 1);
      (kS10, Q_arg 2) ].
  Definition s_regs_zbf_fromout : list (positive * quant) :=
    [ (kA4, Q_arg 0);
      (kS10, Q_arg 1) ].
  Definition s_regs_zbf_fromwin : list (positive * quant) :=
    [ (kA4, Q_arg 0);
      (kS10, Q_arg 1) ].
  Definition s_regs_zbf_w0 : list (positive * quant) :=
    [ (kA4, Q_arg 0);
      (kS10, Q_arg 1);
      (kT2, Q_arg 2) ].
  Definition s_regs_zbf_contig : list (positive * quant) :=
    [ (kA4, Q_arg 0);
      (kS10, Q_arg 1);
      (kT2, Q_arg 2) ].
  Definition s_regs_zbf_wrap : list (positive * quant) :=
    [ (kA4, Q_arg 0);
      (kS10, Q_arg 1);
      (kT2, Q_arg 2) ].
  Definition s_regs_zbf_win : list (positive * quant) :=
    [ (kA4, Q_arg 0);
      (kS10, Q_arg 1) ].
  Definition s_regs_zbf_toofar : list (positive * quant) :=
    [ (kA4, Q_arg 0) ].
  Definition s_regs_zbf_dloop : list (positive * quant) :=
    [ (kA4, Q_arg 0);
      (kS10, Q_arg 1);
      (kT2, Q_arg 2) ].
  Definition s_regs_zbf_dloop_k : list (positive * quant) :=
    [ (kA4, Q_arg 0);
      (kS10, Q_arg 1);
      (kT2, Q_arg 2) ].
  Definition s_regs_zbf_dtail : list (positive * quant) :=
    [ (kA4, Q_arg 0);
      (kS10, Q_arg 1) ].
  Definition s_regs_zbf_direct : list (positive * quant) :=
    [ (kA4, Q_arg 0);
      (kS10, Q_arg 1) ].
  Definition s_regs_zbf_head : list (positive * quant) :=
    [ (kA1, Q_arg 0);
      (kA3, Q_arg 1);
      (kA4, Q_arg 2);
      (kA7, Q_arg 3) ].
  Definition s_regs_zbf_loopx : list (positive * quant) :=
    [ (kA1, Q_arg 0);
      (kA3, Q_arg 1);
      (kA4, Q_arg 2);
      (kA7, Q_arg 3) ].
  (* ---- PATCH: S_GroupBRunBack-rows.tsv md5 : 50 fields ---- *)
  Definition L_LENS_RET : Z := 89244.
  Definition L_DTAB : Z := 89772.
  Definition L_DISTS_RET : Z := 89824.
  Definition L_CL_OK : Z := 91764.
  Definition L_CL_LOOP : Z := 88636.
  Definition L_CL_DLOOP : Z := 88672.
  Definition L_CL_RES : Z := 88752.
  Definition L_CL_P17 : Z := 88836.
  Definition L_CL_X17 : Z := 89008.
  Definition L_CL_P16 : Z := 88896.
  Definition L_CL_X16 : Z := 89044.
  Definition L_CL_P18 : Z := 88956.
  Definition L_CL_X18 : Z := 89104.
  Definition L_CL_CHK : Z := 89132.
  Definition L_CL_FILL : Z := 89144.
  Definition L_CL_FILLX : Z := 89168.
  Definition L_CL_NEXT : Z := 89176.
  Definition L_LVX_CL : Z := 93512.
  Definition L_LEAVE_A7 : Z := 93604.
  Definition L_BADREP0 : Z := 93440.
  Definition L_BADREP : Z := 93356.
  Definition keep_gbb_cp : list positive :=
    [ kRA; kSP; kGP; kTP; kT0; kT1; kS0; kS1; kA0; kA1; kA2; kA3; kA4; kA5; kA6; kS3; kS4; kS5; kS6; kS8; kS9; kT4; kT6 ].
  Definition keep_gbb_cd : list positive :=
    [ kRA; kSP; kGP; kTP; kT1; kT2; kS0; kS1; kA0; kA1; kA2; kA3; kA4; kA5; kA6; kS3; kS4; kS5; kS6; kS8; kS9; kS10; kT6 ].
  Definition keep_gbb_cf : list positive :=
    [ kRA; kSP; kGP; kTP; kT1; kT2; kS0; kS1; kA0; kA1; kA2; kA4; kA5; kA6; kA7; kS2; kS3; kS4; kS5; kS6; kS7; kS8; kS9; kS10; kS11; kT3; kT4; kT6 ].
  Definition keep_gbb_cx : list positive :=
    [ kRA; kSP; kGP; kTP; kT0; kT2; kS0; kA0; kA1; kA3; kA4; kA5; kA6; kA7; kS2; kS3; kS4; kS5; kS6; kS7; kS9; kS10; kT3; kT4; kT6 ].
  Definition keep_gbb_cr : list positive :=
    [ kRA; kSP; kGP; kTP; kS0; kS1; kA0; kA1; kA2; kA4; kA5; kA6; kS3; kS4; kS5; kS6; kS9; kT6 ].
  Definition s_regs_gbb_pull : list (positive * quant) :=
    [ (kS2, Q_arg 0);
      (kS11, Q_arg 1);
      (kT2, Q_arg 2);
      (kA7, Q_arg 2);
      (kT1, Q_arg 3);
      (kS7, Q_arg 4) ].
  Definition s_regs_gbb_pull_lv : list (positive * quant) :=
    [ (kS7, Q_arg 0);
      (kS2, Q_lit 0);
      (kS11, Q_arg 1);
      (kA7, Q_arg 2) ].
  Definition s_regs_gbb_pull_dn : list (positive * quant) :=
    [ (kS2, Q_arg 0);
      (kS11, Q_arg 1);
      (kS10, Q_arg 1);
      (kA7, Q_arg 2);
      (kT2, Q_arg 2);
      (kS7, Q_arg 3) ].
  Definition s_regs_gbb_dec : list (positive * quant) :=
    [ (kSP, Q_arg_at 0 (-224));
      (kS9, Q_lit 67008);
      (kA5, Q_arg_at 1 1384);
      (kA6, Q_arg 2);
      (kT5, Q_arg 3);
      (kS11, Q_arg 3);
      (kS2, Q_arg 4);
      (kT4, Q_arg 5);
      (kA7, Q_arg 5);
      (kS7, Q_arg 6) ].
  Definition s_regs_gbb_dec_lv : list (positive * quant) :=
    [ (kS7, Q_arg 0);
      (kS2, Q_lit 0) ].
  Definition s_regs_gbb_dec_dn : list (positive * quant) :=
    [ (kS11, Q_arg 0);
      (kS2, Q_arg 1);
      (kA7, Q_arg 2);
      (kS7, Q_arg 3);
      (kT0, Q_arg 4);
      (kT3, Q_arg 5);
      (kT4, Q_lit 30);
      (kS9, Q_lit 67008) ].
  Definition s_regs_gbb_stub : list (positive * quant) :=
    [ (kT1, Q_arg 0);
      (kT2, Q_arg 1);
      (kS8, Q_arg 2);
      (kSP, Q_arg_at 3 (-224)) ].
  Definition s_regs_gbb_stub_dn : list (positive * quant) :=
    [ (kS8, Q_arg 0);
      (kS11, Q_arg 1) ].
  Definition s_regs_gbb_fill : list (positive * quant) :=
    [ (kA3, Q_arg 0);
      (kA7, Q_arg 1);
      (kT1, Q_arg 2);
      (kS6, Q_arg_at 3 168) ].
  Definition s_regs_gbb_fill_dn : list (positive * quant) :=
    [ (kA3, Q_arg 0) ].
  Definition s_regs_gbb_res : list (positive * quant) :=
    [ (kSP, Q_arg_at 0 (-224));
      (kS0, Q_arg 1);
      (kS6, Q_arg_at 1 168);
      (kA2, Q_arg 2);
      (kA4, Q_arg 3);
      (kA5, Q_arg_at 1 1384);
      (kA6, Q_arg 4);
      (kA3, Q_arg 5);
      (kS11, Q_arg 6);
      (kS2, Q_arg 7);
      (kA7, Q_arg 8);
      (kS8, Q_arg 9);
      (kS7, Q_arg 10);
      (kT0, Q_arg 11);
      (kT3, Q_arg 12);
      (kT4, Q_lit 30);
      (kS9, Q_lit 67008) ].
  Definition s_regs_gbb_res_lv : list (positive * quant) :=
    [ (kS7, Q_arg 0);
      (kS2, Q_arg 1);
      (kS11, Q_arg 2);
      (kA7, Q_arg 3);
      (kS8, Q_arg 4) ].
  Definition s_regs_gbb_res_bad : list (positive * quant) :=
    [ (kS7, Q_arg 0);
      (kS2, Q_arg 1);
      (kS11, Q_arg 2);
      (kS10, Q_arg 2);
      (kS8, Q_arg 3);
      (kT4, Q_lit 30);
      (kS9, Q_lit 67008) ].
  Definition s_regs_gbb_res_nx : list (positive * quant) :=
    [ (kA3, Q_arg 0);
      (kS7, Q_arg 1);
      (kS2, Q_arg 2);
      (kS11, Q_arg 3);
      (kS8, Q_arg 4);
      (kT4, Q_lit 30);
      (kS9, Q_lit 67008) ].
  Definition s_regs_gbb_chk : list (positive * quant) :=
    [ (kA7, Q_arg 0);
      (kT1, Q_arg 1);
      (kS7, Q_arg 2);
      (kS8, Q_arg 3);
      (kS2, Q_arg 4);
      (kS11, Q_arg 5);
      (kS10, Q_arg 5);
      (kA3, Q_arg 6);
      (kT4, Q_lit 30);
      (kS9, Q_lit 67008);
      (kA4, Q_arg 7);
      (kS0, Q_arg 8);
      (kS6, Q_arg_at 8 168) ].
  Definition s_regs_gbb_x16 : list (positive * quant) :=
    [ (kS2, Q_arg 0);
      (kS11, Q_arg 1);
      (kS10, Q_arg 1);
      (kA7, Q_arg 2);
      (kS7, Q_arg 3);
      (kT0, Q_arg 4);
      (kA3, Q_arg 5);
      (kS6, Q_arg_at 6 168);
      (kT4, Q_lit 30);
      (kS9, Q_lit 67008);
      (kS0, Q_arg 6);
      (kA4, Q_arg 7) ].
  Definition s_regs_gbb_x1718 : list (positive * quant) :=
    [ (kS2, Q_arg 0);
      (kS11, Q_arg 1);
      (kS10, Q_arg 1);
      (kA7, Q_arg 2);
      (kS7, Q_arg 3);
      (kT0, Q_arg 4);
      (kA3, Q_arg 5);
      (kS6, Q_arg_at 6 168);
      (kT4, Q_lit 30);
      (kS9, Q_lit 67008);
      (kS0, Q_arg 6);
      (kA4, Q_arg 7) ].
  Definition s_regs_gbb_loop : list (positive * quant) :=
    [ (kSP, Q_arg_at 0 (-224));
      (kS0, Q_arg 1);
      (kS6, Q_arg_at 1 168);
      (kA2, Q_arg 2);
      (kA4, Q_arg 3);
      (kA5, Q_arg_at 1 1384);
      (kA6, Q_arg 4);
      (kA3, Q_arg 5);
      (kS11, Q_arg 6);
      (kT2, Q_arg 6);
      (kS2, Q_arg 7);
      (kT1, Q_arg 7);
      (kS8, Q_arg 8);
      (kS7, Q_arg 9);
      (kT4, Q_lit 30);
      (kS9, Q_lit 67008) ].
  Definition s_regs_gbb_loop_xd : list (positive * quant) :=
    [ (kS7, Q_arg 0);
      (kS2, Q_lit 0);
      (kT1, Q_arg 1);
      (kT2, Q_arg 2);
      (kS8, Q_arg 3) ].
  Definition s_regs_gbb_loop_xa : list (positive * quant) :=
    [ (kS7, Q_arg 0);
      (kS2, Q_arg 1);
      (kS11, Q_arg 2);
      (kA7, Q_arg 3) ].
  Definition s_regs_gbb_loop_bad : list (positive * quant) :=
    [ (kS7, Q_arg 0);
      (kS2, Q_arg 1);
      (kS11, Q_arg 2);
      (kS10, Q_arg 2);
      (kS8, Q_arg 3);
      (kT4, Q_lit 30);
      (kS9, Q_lit 67008) ].
  Definition s_regs_gbb_loop_dn : list (positive * quant) :=
    [ (kS7, Q_arg 0);
      (kS2, Q_arg 1);
      (kS11, Q_arg 2);
      (kS8, Q_arg 3);
      (kA3, Q_arg 4);
      (kT4, Q_lit 30);
      (kS9, Q_lit 67008) ].
  Definition s_regs_gbb_loop_res : list (positive * quant) :=
    [ (kSP, Q_arg_at 0 (-224));
      (kS0, Q_arg 1);
      (kS6, Q_arg_at 1 168);
      (kA2, Q_arg 2);
      (kA4, Q_arg 3);
      (kA5, Q_arg_at 1 1384);
      (kA6, Q_arg 4);
      (kA3, Q_arg 5);
      (kS11, Q_arg 6);
      (kS2, Q_arg 7);
      (kA7, Q_arg 8);
      (kS8, Q_arg 9);
      (kS7, Q_arg 10);
      (kT0, Q_arg 11);
      (kT3, Q_arg 12);
      (kT4, Q_lit 30);
      (kS9, Q_lit 67008);
      (kT1, Q_arg 13);
      (kT2, Q_arg 14) ].
  Definition f_gbb_stub : list fslot :=
    [ ("ret"%string, (-160), W8, Q_arg 0) ].
  (* ---- PATCH: S_GroupBRunFront-rows.tsv md5 : 36 fields ---- *)
  Definition L_CL_HEAD : Z := 88592.
  Definition L_CL_DONE : Z := 89188.
  Definition L_TAB_LOOP : Z := 87376.
  Definition L_TAB_BODY : Z := 88172.
  Definition L_LL_BODY : Z := 88304.
  Definition L_LL_HEAD : Z := 88352.
  Definition L_LL_FILL0 : Z := 88396.
  Definition L_LL_FLOOP : Z := 88440.
  Definition L_LL_FEND : Z := 88476.
  Definition A_GB_ORDER : Z := 67132.
  Definition keep_gb_ll : list positive :=
    [ kRA; kSP; kGP; kTP; kS0; kS1; kA0; kA1; kS3; kS4; kS5; kS6; kS9; kS10; kT4; kT6 ].
  Definition keep_gb_tb : list positive :=
    [ kRA; kSP; kGP; kTP; kS0; kS1; kA0; kA1; kS3; kS4; kS5; kS6; kS9; kT4; kT6 ].
  Definition keep_gb_lf : list positive :=
    [ kRA; kSP; kGP; kTP; kS0; kS1; kA0; kS2; kS3; kS4; kS5; kS6; kS7; kS8; kS9; kS10; kS11; kT4; kT6 ].
  Definition L_TAB_SKIP : Z := 88168.
  Definition L_LL_SETUP : Z := 88260.
  Definition L_LL_FILL : Z := 88404.
  Definition L_LL_TABLE : Z := 88480.
  Definition L_LL_RET : Z := 88532.
  Definition L_TBLERR : Z := 89840.
  Definition L_BAD_TAB : Z := 89284.
  Definition s_regs_gb_cl : list (positive * quant) :=
    [ (kS11, Q_next_in);
      (kA3, Q_arg 0) ].
  Definition s_regs_gb_cld : list (positive * quant) :=
    [ (kS11, Q_next_in);
      (kA2, Q_arg 0);
      (kA4, Q_arg 1) ].
  Definition s_regs_gb_ll_head : list (positive * quant) :=
    [ (kS0, Q_arg 0);
      (kS6, Q_arg_at 0 168);
      (kA3, Q_arg 1);
      (kA4, Q_arg 2);
      (kA5, Q_arg 3);
      (kA2, Q_arg 4);
      (kS8, Q_arg 5);
      (kS7, Q_arg 6);
      (kS2, Q_arg 7);
      (kS11, Q_arg 8) ].
  Definition s_regs_gb_ll_kx : list (positive * quant) :=
    [ (kS8, Q_arg 0);
      (kS7, Q_arg 1);
      (kS2, Q_lit 0);
      (kS11, Q_arg 2) ].
  Definition s_regs_gb_ll_kd : list (positive * quant) :=
    [ (kS8, Q_arg 0);
      (kS7, Q_arg 1);
      (kS2, Q_arg 2);
      (kS11, Q_arg 3);
      (kA2, Q_arg 4);
      (kS0, Q_arg 5);
      (kS6, Q_arg_at 5 168) ].
  Definition s_regs_gb_ll_body : list (positive * quant) :=
    [ (kS0, Q_arg 0);
      (kS6, Q_arg_at 0 168);
      (kA3, Q_arg 1);
      (kA4, Q_arg 2);
      (kA5, Q_arg 3);
      (kA2, Q_arg 4);
      (kS8, Q_arg 5);
      (kS7, Q_arg 6);
      (kS2, Q_arg 7);
      (kS11, Q_arg 8) ].
  Definition s_regs_gb_fl_head : list (positive * quant) :=
    [ (kS6, Q_arg_at 0 168);
      (kA0, Q_lit 4294967295);
      (kA1, Q_arg 1);
      (kA5, Q_arg 2) ].
  Definition s_regs_gb_fl_k : list (positive * quant) :=
    [ (kA2, Q_lit 19) ].
  Definition s_regs_gb_tl_head : list (positive * quant) :=
    [ (kS8, Q_arg 0);
      (kA2, Q_arg 0);
      (kS11, Q_arg 1);
      (kS2, Q_arg 2);
      (kS7, Q_arg 3) ].
  Definition s_regs_gb_tl_lv : list (positive * quant) :=
    [ (kS11, Q_arg 0);
      (kS2, Q_lit 0);
      (kS7, Q_arg 1);
      (kS8, Q_arg 2) ].
  Definition s_regs_gb_tl_dn : list (positive * quant) :=
    [ (kS10, Q_arg 0);
      (kS11, Q_arg 0);
      (kS2, Q_arg 1);
      (kS7, Q_arg 2);
      (kS8, Q_arg 3) ].
  Definition s_regs_gb_llt : list (positive * quant) :=
    [ (kSP, Q_u_at (-224));
      (kGP, Q_entry kGP);
      (kTP, Q_entry kTP);
      (kS0, Q_p);
      (kS6, Q_p_at 168);
      (kS4, Q_lit 16209);
      (kS9, Q_lit JTAB_ADDR);
      (kS1, Q_avail_out);
      (kS11, Q_next_in) ].
  Definition s_regs_gb_llfill : list (positive * quant) :=
    [ (kA5, Q_arg 0) ].
  Definition s_regs_gb_llsetup : list (positive * quant) :=
    [ (kS11, Q_next_in);
      (kA5, Q_arg 0);
      (kA2, Q_arg 1) ].
  Definition s_regs_gb_tbody : list (positive * quant) :=
    [ (kS2, Q_arg 0);
      (kS3, Q_next_out);
      (kRA, Q_avail_out);
      (kS7, Q_arg 1);
      (kS8, Q_arg 2);
      (kS11, Q_arg 3);
      (kS10, Q_arg 3) ].
  Definition s_regs_gb_tbody_jb : list (positive * quant) :=
    [ (kSP, Q_u_at (-224));
      (kGP, Q_entry kGP);
      (kTP, Q_entry kTP);
      (kS0, Q_p);
      (kA0, Q_u);
      (kA1, Q_lit 0);
      (kS6, Q_p_at 168);
      (kT6, Q_lit (-16180));
      (kT4, Q_lit 30);
      (kS9, Q_lit JTAB_ADDR);
      (kS4, Q_lit 16209);
      (kS2, Q_arg 0);
      (kS3, Q_next_out);
      (kRA, Q_avail_out);
      (kS10, Q_arg 1);
      (kS7, Q_arg 2);
      (kS8, Q_arg 3) ].
  (* ---- PATCH: S_TopI-rows.tsv md5 : 21 fields ---- *)
  Definition L_EPI_S : Z := 85772.
  Definition L_HEAD_LOOP : Z := 87028.
  Definition L_HEAD_BODY : Z := 89476.
  Definition L_HEAD_WERR : Z := 93292.
  Definition L_HEAD_FIN : Z := 93456.
  Definition L_DICTID_LOOP : Z := 87212.
  Definition L_DICTID_BODY : Z := 87680.
  Definition s_regs_top_epi : list (positive * quant) :=
    [ (kSP, Q_arg 0) ].
  Definition keep_top_epi : list positive :=
    [ kGP; kTP; kS5; kS6; kS7; kS8; kS9; kS10; kS11 ].
  Definition s_regs_top_head_body : list (positive * quant) :=
    [ (kS10, Q_next_in);
      (kA2, Q_lit 5) ].
  Definition s_regs_top_head_werr : list (positive * quant) :=
    [ (kSP, Q_u_at (-224));
      (kGP, Q_entry kGP);
      (kTP, Q_entry kTP);
      (kS0, Q_p);
      (kS4, Q_lit 16209);
      (kS2, Q_avail_in);
      (kS3, Q_next_out);
      (kS1, Q_avail_out);
      (kS10, Q_next_in);
      (kS8, Q_bits);
      (kA1, Q_par);
      (kS6, Q_p_at 168);
      (kS9, Q_lit JTAB_ADDR) ].
  Definition s_regs_top_head_fin : list (positive * quant) :=
    [ (kSP, Q_u_at (-224));
      (kGP, Q_entry kGP);
      (kTP, Q_entry kTP);
      (kS0, Q_p);
      (kS4, Q_lit 16209);
      (kS2, Q_avail_in);
      (kS3, Q_next_out);
      (kS1, Q_avail_out);
      (kS10, Q_next_in);
      (kA0, Q_par);
      (kS6, Q_p_at 168);
      (kS9, Q_lit JTAB_ADDR) ].
  Definition s_regs_top_head_loop : list (positive * quant) :=
    [ (kS0, Q_p);
      (kS8, Q_bits);
      (kA3, Q_bits);
      (kS11, Q_next_in);
      (kS2, Q_avail_in);
      (kS7, Q_hold) ].
  Definition s_regs_top_head_lv : list (positive * quant) :=
    [ (kS11, Q_next_in);
      (kS2, Q_avail_in);
      (kS7, Q_hold);
      (kS8, Q_bits) ].
  Definition s_regs_top_head_dn : list (positive * quant) :=
    [ (kS11, Q_next_in);
      (kS10, Q_next_in);
      (kS2, Q_avail_in);
      (kS7, Q_hold);
      (kS8, Q_bits) ].
  Definition keep_top_head_loop : list positive :=
    [ kSP; kGP; kTP; kS0; kA0; kA1; kA2; kS1; kRA; kS3; kS4; kS6; kT4; kS9; kT6 ].
  Definition s_regs_top_dictid_loop : list (positive * quant) :=
    [ (kS0, Q_p);
      (kS8, Q_bits);
      (kA3, Q_bits);
      (kS11, Q_next_in);
      (kS2, Q_avail_in);
      (kS7, Q_hold) ].
  Definition s_regs_top_dictid_lv : list (positive * quant) :=
    [ (kS11, Q_next_in);
      (kS2, Q_avail_in);
      (kS7, Q_hold);
      (kS8, Q_bits) ].
  Definition s_regs_top_dictid_dn : list (positive * quant) :=
    [ (kA2, Q_next_in);
      (kS11, Q_next_in);
      (kS2, Q_avail_in);
      (kS7, Q_hold);
      (kS8, Q_bits) ].
  Definition keep_top_dictid_loop : list positive :=
    [ kSP; kGP; kTP; kS0; kA0; kA1; kS1; kRA; kS3; kS4; kS6; kT4; kS9; kT6 ].
  Definition s_regs_top_dictid_body : list (positive * quant) :=
    [ (kA2, Q_next_in) ].
  (* ---- PATCH: S_ZBI-rows.tsv md5 : 21 fields ---- *)
  Definition L_ZBI_OFFS : Z := 96448.
  Definition L_ZBI_SORT : Z := 96560.
  Definition L_ZBI_SORT_NEXT : Z := 96588.
  Definition L_ZBI_SORT_LOOP : Z := 96600.
  Definition L_ZBI_SUB : Z := 97116.
  Definition L_ZBI_SUB_NEW : Z := 97128.
  Definition L_ZBI_CURRSZ : Z := 97140.
  Definition L_ZBI_CURR_LOOP : Z := 97160.
  Definition L_ZBI_ENOUGH : Z := 97208.
  Definition L_ZBI_ENOUGH_D : Z := 97236.
  Definition L_ZBI_LINK : Z := 97256.
  Definition s_regs_zbi_offs : list (positive * quant) :=
    [ (kT0, Q_arg 0);
      (kT1, Q_arg 1);
      (kA7, Q_arg 2);
      (kT4, Q_arg 3);
      (kT5, Q_arg 4);
      (kT6, Q_arg 5);
      (kS0, Q_arg 6);
      (kS1, Q_arg 7);
      (kS2, Q_arg 8);
      (kS3, Q_arg 9);
      (kS4, Q_arg 10);
      (kS5, Q_arg 11);
      (kS6, Q_arg 12);
      (kS7, Q_arg 13);
      (kS8, Q_arg 14);
      (kS9, Q_arg 15);
      (kS10, Q_arg 16) ].
  Definition s_regs_zbi_sort : list (positive * quant) :=
    [ (kA6, Q_arg 0);
      (kT3, Q_arg 1);
      (kT2, Q_arg 2);
      (kT0, Q_arg 3);
      (kT1, Q_arg 4);
      (kA7, Q_arg 5) ].
  Definition s_regs_zbi_u : list (positive * quant) :=
    [ (kT6, Q_arg 0);
      (kT1, Q_arg 1);
      (kS1, Q_arg 2);
      (kS0, Q_arg 3);
      (kA2, Q_arg 4);
      (kS8, Q_arg 5) ].
  Definition s_regs_zbi_curr : list (positive * quant) :=
    [ (kT5, Q_arg 0);
      (kS9, Q_arg 1);
      (kS10, Q_arg 2);
      (kA6, Q_arg 3);
      (kS7, Q_arg 4) ].
  Definition s_regs_zbi_enough : list (positive * quant) :=
    [ (kT5, Q_arg 0);
      (kS9, Q_arg 1);
      (kS7, Q_arg 2);
      (kA6, Q_arg 3) ].
  Definition s_regs_zbi_link : list (positive * quant) :=
    [ (kS9, Q_arg 0);
      (kS7, Q_arg 1);
      (kT5, Q_arg 2) ].
  Definition s_regs_zbi_currsz : list (positive * quant) :=
    [ (kS9, Q_arg 0);
      (kT5, Q_arg 1) ].
  Definition s_regs_zbi_subnew : list (positive * quant) :=
    [ (kA6, Q_arg 0);
      (kT5, Q_arg 1) ].
  Definition FR_ZBI_OFFS : Z := (-166).
  Definition FR_ZBI_OFFS0 : Z := (-168).
  (* ---- PATCH: S_It3-rows.tsv md5 : 52 fields ---- *)
  Definition L_IT3_COUNT : Z := 95788.
  Definition L_IT3_CLOOP : Z := 95812.
  Definition L_IT3_MAXE : Z := 95844.
  Definition L_IT3_MAX14 : Z := 95868.
  Definition L_IT3_MAX13 : Z := 95888.
  Definition L_IT3_MAX12 : Z := 95908.
  Definition L_IT3_MAX11 : Z := 95928.
  Definition L_IT3_MAX10 : Z := 95948.
  Definition L_IT3_MAX9 : Z := 95968.
  Definition L_IT3_MAX8 : Z := 95988.
  Definition L_IT3_MAX7 : Z := 96008.
  Definition L_IT3_MAX6 : Z := 96028.
  Definition L_IT3_MAX5 : Z := 96048.
  Definition L_IT3_MAX4 : Z := 96068.
  Definition L_IT3_MAX3 : Z := 96088.
  Definition L_IT3_MAX2 : Z := 96108.
  Definition L_IT3_ROOT : Z := 96124.
  Definition L_IT3_ROOT1 : Z := 96132.
  Definition L_IT3_MINLOOP : Z := 96148.
  Definition L_IT3_MINDONE : Z := 96176.
  Definition L_IT3_LEFT : Z := 96184.
  Definition L_IT3_FILL : Z := 96928.
  Definition L_IT3_FLOOP : Z := 96948.
  Definition L_IT3_INCR : Z := 96988.
  Definition L_IT3_ILOOP : Z := 96996.
  Definition L_IT3_IDONE : Z := 97016.
  Definition L_IT3_ST1 : Z := 97116.
  Definition L_IT3_LOW : Z := 97432.
  Definition F_IT3_SP : Z := (-192).
  Definition F_IT3_COUNT : Z := (-136).
  Definition F_IT3_COUNT_END : Z := (-104).
  Definition F_IT3_SV1 : Z := (-8).
  Definition F_IT3_SV8 : Z := (-16).
  Definition F_IT3_SV9 : Z := (-24).
  Definition F_IT3_SV18 : Z := (-32).
  Definition F_IT3_SV19 : Z := (-40).
  Definition F_IT3_SV20 : Z := (-48).
  Definition F_IT3_SV21 : Z := (-56).
  Definition F_IT3_SV22 : Z := (-64).
  Definition F_IT3_SV23 : Z := (-72).
  Definition F_IT3_SV24 : Z := (-80).
  Definition F_IT3_SV25 : Z := (-88).
  Definition F_IT3_SV26 : Z := (-96).
  Definition F_IT3_SV27 : Z := (-104).
  Definition keys_it3_entry : list positive :=
    [ kSP; kRA; kGP; kTP; kS0; kS1; kA0; kA1; kA2; kA3; kA4; kA5; kS2; kS3; kS4; kS5; kS6; kS7; kS8; kS9; kS10; kS11 ].
  Definition keys_it3_p : list positive :=
    [ kSP; kGP; kTP; kA0; kA1; kA2; kA3; kA4; kA5 ].
  Definition keys_it3_cloop : list positive :=
    [ kT0; kA6; kA7 ].
  Definition keys_it3_a7 : list positive :=
    [ kA7 ].
  Definition keys_it3_kmax : list positive :=
    [ kA7; kT0; kT2 ].
  Definition keys_it3_mloop : list positive :=
    [ kT1; kA6; kT4; kT0; kA7; kT3; kT2 ].
  Definition keys_it3_mdone : list positive :=
    [ kT1; kT0; kA7; kT3; kT2 ].
  Definition keys_it3_left : list positive :=
    [ kT0; kT1; kA7; kT3; kT2 ].
  (* ---- PATCH: S_It3RunBack-rows.tsv md5 : 12 fields ---- *)
  Definition A_it3b_lext : Z := 67232.
  Definition A_it3b_dext : Z := 67358.
  Definition A_it3b_lbase : Z := 67170.
  Definition A_it3b_dbase : Z := 67294.
  Definition s_regs_it3b_c : list (positive * quant) :=
    [ (kSP, Q_arg_at 0 (-192));
      (kGP, Q_arg 1);
      (kTP, Q_arg 2);
      (kA1, Q_arg 3);
      (kA3, Q_arg 4);
      (kA4, Q_arg 5);
      (kA5, Q_arg 6);
      (kA7, Q_arg 7);
      (kT0, Q_arg 8);
      (kA0, Q_arg 9);
      (kT3, Q_arg 10);
      (kT2, Q_arg 11);
      (kS2, Q_lit 1);
      (kS3, Q_lit (-1));
      (kS4, Q_arg 12);
      (kS5, Q_arg_at 0 (-136)) ].
  Definition s_regs_it3b_s : list (positive * quant) :=
    [ (kT6, Q_arg 0);
      (kT1, Q_arg 1);
      (kA6, Q_arg 2);
      (kT5, Q_arg 3);
      (kS1, Q_arg 4);
      (kS0, Q_arg 5);
      (kA2, Q_arg 6);
      (kS7, Q_arg 7) ].
  Definition s_regs_it3b_ov : list (positive * quant) :=
    [ (kS10, Q_arg 0);
      (kS9, Q_arg 1) ].
  Definition s_regs_it3b_hb : list (positive * quant) :=
    [ (kS8, Q_arg 0) ].
  Definition s_regs_it3b_floop : list (positive * quant) :=
    [ (kS6, Q_arg 0);
      (kS11, Q_arg 1);
      (kRA, Q_arg 2) ].
  Definition s_regs_it3b_incr : list (positive * quant) :=
    [ (kS6, Q_arg 0) ].
  Definition s_regs_it3b_incrk : list (positive * quant) :=
    [ (kS9, Q_arg 0) ].
  Definition fr_it3b_sl : list fslot :=
    [ ("isd"%string, (-184), W8, Q_arg 0);
      ("isl"%string, (-176), W8, Q_arg 1) ].
  (* ---- PATCH: S_ZBF-rows2.tsv md5 : 23 fields ---- *)
  Definition s_regs_zbf_const : list (positive * quant) :=
    [ (kA0, Q_arg 0);
      (kA2, Q_arg 1);
      (kA5, Q_arg 2);
      (kA6, Q_arg 3);
      (kS0, Q_arg 4);
      (kS1, Q_arg 5);
      (kS2, Q_arg 6);
      (kS3, Q_arg 7);
      (kS4, Q_arg 8);
      (kS6, Q_arg 9);
      (kS7, Q_arg 10);
      (kS8, Q_arg 11);
      (kT0, Q_lit (-1));
      (kT1, Q_lit 14);
      (kT3, Q_lit 2);
      (kT4, Q_arg 12);
      (kT5, Q_arg 13);
      (kT6, Q_arg 14);
      (kSP, Q_arg_at 15 (-112));
      (kGP, Q_arg 16);
      (kTP, Q_arg 17) ].
  Definition s_regs_zbf_exit : list (positive * quant) :=
    [ (kA0, Q_arg 0);
      (kA2, Q_arg 1);
      (kA5, Q_arg 2);
      (kA6, Q_arg 3);
      (kSP, Q_arg_at 4 (-112));
      (kGP, Q_arg 5);
      (kTP, Q_arg 6);
      (kA1, Q_arg 7);
      (kA3, Q_arg 8);
      (kA4, Q_arg 9);
      (kA7, Q_arg 10) ].
  Definition s_regs_zbf_xpre : list (positive * quant) :=
    [ (kA0, Q_arg 0);
      (kA2, Q_arg 1);
      (kA5, Q_arg 2);
      (kA6, Q_arg 3);
      (kSP, Q_arg_at 4 (-112));
      (kGP, Q_arg 5);
      (kTP, Q_arg 6);
      (kA1, Q_arg 7);
      (kA3, Q_arg 8);
      (kA4, Q_arg 9);
      (kA7, Q_arg 10) ].
  Definition s_regs_zbf_latch : list (positive * quant) :=
    [ (kA1, Q_arg 0);
      (kA3, Q_arg 1);
      (kA4, Q_arg 2);
      (kA7, Q_arg 3) ].
  Definition s_regs_zbf_exit0 : list (positive * quant) :=
    [ (kSP, Q_arg 0);
      (kGP, Q_arg 1);
      (kTP, Q_arg 2) ].
  Definition s_regs_zbf_entry : list (positive * quant) :=
    [ (kA0, Q_arg 0);
      (kA1, Q_arg 1);
      (kSP, Q_arg 2);
      (kRA, Q_arg 3);
      (kGP, Q_arg 4);
      (kTP, Q_arg 5) ].
  Definition s_regs_zbf_eob : list (positive * quant) :=
    [ (kS9, Q_arg 0) ].
  Definition s_regs_zbf_look : list (positive * quant) :=
    [ (kA1, Q_arg 0);
      (kA3, Q_arg 1);
      (kA4, Q_arg 2);
      (kA7, Q_arg 3) ].
  Definition s_regs_zbf_lit : list (positive * quant) :=
    [ (kA1, Q_arg 0);
      (kA3, Q_arg 1);
      (kA4, Q_arg 2);
      (kA7, Q_arg 3);
      (kT2, Q_arg 4) ].
  Definition s_regs_zbf_lenb : list (positive * quant) :=
    [ (kA1, Q_arg 0);
      (kA3, Q_arg 1);
      (kA4, Q_arg 2);
      (kA7, Q_arg 3);
      (kT2, Q_arg 4);
      (kS9, Q_arg 5) ].
  Definition s_regs_zbf_eobk : list (positive * quant) :=
    [ (kA1, Q_arg 0);
      (kA3, Q_arg 1);
      (kA4, Q_arg 2);
      (kA7, Q_arg 3);
      (kS9, Q_arg 4) ].
  Definition s_regs_zbf_dlook : list (positive * quant) :=
    [ (kA1, Q_arg 0);
      (kA3, Q_arg 1);
      (kA4, Q_arg 2);
      (kA7, Q_arg 3);
      (kS10, Q_arg 4) ].
  Definition s_regs_zbf_lenj : list (positive * quant) :=
    [ (kA1, Q_arg 0);
      (kA3, Q_arg 1);
      (kA4, Q_arg 2);
      (kA7, Q_arg 3);
      (kS10, Q_arg 4) ].
  Definition s_regs_zbf_lenj2 : list (positive * quant) :=
    [ (kA1, Q_arg 0);
      (kA3, Q_arg 1);
      (kA4, Q_arg 2);
      (kA7, Q_arg 3);
      (kS10, Q_arg 4);
      (kT2, Q_arg 5) ].
  Definition s_regs_zbf_distb : list (positive * quant) :=
    [ (kA1, Q_arg 0);
      (kA3, Q_arg 1);
      (kA4, Q_arg 2);
      (kA7, Q_arg 3);
      (kS10, Q_arg 4);
      (kT2, Q_arg 5);
      (kS11, Q_arg 6) ].
  Definition s_regs_zbf_baddk : list (positive * quant) :=
    [ (kA1, Q_arg 0);
      (kA3, Q_arg 1);
      (kA4, Q_arg 2);
      (kA7, Q_arg 3) ].
  Definition s_regs_zbf_directk : list (positive * quant) :=
    [ (kA1, Q_arg 0);
      (kA3, Q_arg 1);
      (kA4, Q_arg 2);
      (kA7, Q_arg 3);
      (kS10, Q_arg 4);
      (kS11, Q_arg 5) ].
  Definition s_regs_zbf_wink : list (positive * quant) :=
    [ (kA1, Q_arg 0);
      (kA3, Q_arg 1);
      (kA4, Q_arg 2);
      (kA7, Q_arg 3);
      (kS10, Q_arg 4);
      (kS11, Q_arg 5) ].
  Definition s_regs_zbf_distj : list (positive * quant) :=
    [ (kA1, Q_arg 0);
      (kA3, Q_arg 1);
      (kA4, Q_arg 2);
      (kS9, Q_arg 3);
      (kS10, Q_arg 4);
      (kT2, Q_arg 5);
      (kRA, Q_arg 6) ].
  Definition fr_zbf_entry : list fslot :=
    [ ("ra"%string, (-8), W8, Q_par);
      ("s0"%string, (-16), W8, Q_entry kS0);
      ("s1"%string, (-24), W8, Q_entry kS1);
      ("s2"%string, (-32), W8, Q_entry kS2);
      ("s3"%string, (-40), W8, Q_entry kS3);
      ("s4"%string, (-48), W8, Q_entry kS4);
      ("s5"%string, (-56), W8, Q_entry kS5);
      ("s6"%string, (-64), W8, Q_entry kS6);
      ("s7"%string, (-72), W8, Q_entry kS7);
      ("s8"%string, (-80), W8, Q_entry kS8);
      ("s9"%string, (-88), W8, Q_entry kS9);
      ("s10"%string, (-96), W8, Q_entry kS10);
      ("s11"%string, (-104), W8, Q_entry kS11) ].
  Definition fr_zbf_local : list fslot :=
    [ ("wsum"%string, (-112), W8, Q_arg 0) ].
  Definition FR_ZBF_LO : Z := (-112).
  Definition FR_ZBF_EXT : Z := 112.
  (* ---- PATCH: S_GroupBRunBack-rows-add2.tsv md5 : 2 fields ---- *)
  Definition f_gbb_jt : list fslot :=
    [].
  Definition s_regs_gbb_stub_k : list (positive * quant) :=
    [ (kS8, Q_arg 0);
      (kS11, Q_arg 1);
      (kS1, Q_arg 2) ].
  (* ---- PATCH: S_LenF-back-rows-P-r1.tsv md5 : 19 fields ---- *)
  Definition L_LLOOP1 : Z := 91996.
  Definition L_L40 : Z := 92068.
  Definition L_LLOOP2 : Z := 92164.
  Definition L_L700 : Z := 92268.
  Definition L_LX34 : Z := 87124.
  Definition L_L770 : Z := 92376.
  Definition L_L778 : Z := 92384.
  Definition L_LSLOW : Z := 91932.
  Definition L_L28 : Z := 92304.
  Definition L_FRET : Z := 91868.
  Definition A_lenb_badmsg : Z := 66608.
  Definition s_regs_lenb_l1 : list (positive * quant) :=
    [ (kA5, Q_arg 0);
      (kA6, Q_arg 1);
      (kA2, Q_arg 2);
      (kT1, Q_arg 3);
      (kT0, Q_arg 4);
      (kA3, Q_arg 4);
      (kS7, Q_arg 5);
      (kA4, Q_arg 6);
      (kA7, Q_arg 7);
      (kS2, Q_arg 8);
      (kS8, Q_arg 9);
      (kS11, Q_arg 10) ].
  Definition s_regs_lenb_l1_lv : list (positive * quant) :=
    [ (kS7, Q_arg 0) ].
  Definition s_regs_lenb_l1_dn : list (positive * quant) :=
    [ (kS10, Q_arg 0);
      (kA2, Q_arg 1);
      (kA3, Q_arg 2);
      (kT0, Q_arg 2);
      (kS7, Q_arg 3);
      (kA4, Q_arg 4);
      (kA7, Q_arg 5) ].
  Definition keep_lenb_e1 : list positive :=
    [ kRA; kSP; kGP; kTP; kS0; kS1; kA0; kA1; kA5; kA6; kS2; kS3; kS4; kS6; kS8; kS9; kS11; kT3; kT4; kT6 ].
  Definition s_regs_lenb_l2 : list (positive * quant) :=
    [ (kT2, Q_arg 0);
      (kA6, Q_arg 1);
      (kA7, Q_arg 2);
      (kA5, Q_arg 3);
      (kA2, Q_arg 4);
      (kA3, Q_arg 5);
      (kS10, Q_arg 6);
      (kT0, Q_arg 7);
      (kS1, Q_arg 8);
      (kT4, Q_arg 9);
      (kT1, Q_arg 9);
      (kS7, Q_arg 10);
      (kT5, Q_arg 11);
      (kT3, Q_arg 12) ].
  Definition s_regs_lenb_l2_lv : list (positive * quant) :=
    [ (kS7, Q_arg 0) ].
  Definition s_regs_lenb_l2_dn : list (positive * quant) :=
    [ (kT6, Q_arg 0);
      (kT0, Q_arg 1);
      (kT1, Q_arg 2);
      (kT4, Q_arg 2);
      (kS7, Q_arg 3);
      (kT5, Q_arg 4);
      (kT3, Q_arg 5) ].
  Definition keep_lenb_e2 : list positive :=
    [ kRA; kSP; kGP; kTP; kT2; kS0; kA0; kA1; kA2; kA3; kA4; kA5; kA6; kA7; kS3; kS4; kS6; kS8; kS9; kS10; kS11 ].
  (* ---- PATCH: S_LenF-back-rows-P-part2-r1.tsv md5 : 5 fields ---- *)
  Definition s_regs_lenb_e : list (positive * quant) :=
    [ (kSP, Q_u_at (-224));
      (kGP, Q_entry kGP);
      (kTP, Q_entry kTP);
      (kS0, Q_p);
      (kA0, Q_u);
      (kA1, Q_lit 0);
      (kS6, Q_p_at 168);
      (kS4, Q_lit 16209);
      (kS3, Q_next_out);
      (kRA, Q_avail_out);
      (kS9, Q_lit JTAB_ADDR) ].
  Definition s_regs_lenb_j28 : list (positive * quant) :=
    [ (kT6, Q_lit (-16180));
      (kT4, Q_lit 30);
      (kS9, Q_lit JTAB_ADDR);
      (kS11, Q_p_at 7160);
      (kT2, Q_arg 0);
      (kA7, Q_arg 1);
      (kA4, Q_arg 2);
      (kA6, Q_arg 3);
      (kA3, Q_arg 4);
      (kS7, Q_arg 5);
      (kS10, Q_arg 6);
      (kA2, Q_arg 7) ].
  Definition s_regs_lenb_kx1 : list (positive * quant) :=
    [ (kS7, Q_arg 0);
      (kS2, Q_avail_in);
      (kS8, Q_bits);
      (kS11, Q_next_in) ].
  Definition s_regs_lenb_j40 : list (positive * quant) :=
    [ (kT6, Q_lit (-16180));
      (kT4, Q_lit 30);
      (kS9, Q_lit JTAB_ADDR);
      (kS2, Q_avail_in);
      (kS8, Q_bits);
      (kS11, Q_next_in);
      (kA5, Q_arg 0);
      (kA6, Q_arg 1);
      (kS10, Q_arg 2);
      (kA2, Q_arg 3);
      (kA3, Q_arg 4);
      (kS7, Q_arg 5);
      (kA7, Q_arg 6);
      (kA4, Q_arg 7) ].
  Definition s_regs_lenb_j700 : list (positive * quant) :=
    [ (kA5, Q_arg 0);
      (kA6, Q_arg 1);
      (kA7, Q_arg 2);
      (kS11, Q_p_at 7160);
      (kA4, Q_arg 1);
      (kA2, Q_arg 3);
      (kA3, Q_arg 4);
      (kS10, Q_arg 5);
      (kT6, Q_arg 6);
      (kT0, Q_arg 7);
      (kT1, Q_arg 8);
      (kS7, Q_arg 9);
      (kT5, Q_arg 10);
      (kT3, Q_arg 11) ].
  (* ---- PATCH: S_LenF-back-rows-P-part3-r1.tsv md5 : 5 fields ---- *)
  Definition s_regs_lenb_l778 : list (positive * quant) :=
    [ (kA6, Q_arg 0);
      (kT1, Q_p_at 7160) ].
  Definition s_regs_lenb_lx34 : list (positive * quant) :=
    [ (kA3, Q_arg 0) ].
  Definition s_regs_lenb_j60 : list (positive * quant) :=
    [ (kA5, Q_arg 0);
      (kA2, Q_arg 1);
      (kA4, Q_arg 2);
      (kS7, Q_arg 3);
      (kA3, Q_arg 4) ].
  Definition L_LENB_RELOAD_J : Z := 91732.
  Definition s_regs_lenb_jra : list (positive * quant) :=
    [ (kSP, Q_u_at (-224));
      (kGP, Q_entry kGP);
      (kTP, Q_entry kTP);
      (kS0, Q_p);
      (kA0, Q_u);
      (kA1, Q_lit 0);
      (kS4, Q_lit 16209);
      (kS6, Q_p_at 168);
      (kS9, Q_lit JTAB_ADDR);
      (kS10, Q_arg 0);
      (kS2, Q_arg 1);
      (kS3, Q_arg 2);
      (kRA, Q_arg 3);
      (kS7, Q_arg 4);
      (kS8, Q_arg 5) ].
  (* ---- PATCH: S_LenF-rows.tsv md5 : 51 fields ---- *)
  Definition L_MLOOP : Z := 93144.
  Definition L_MAFTER : Z := 93168.
  Definition L_SETLEN : Z := 93184.
  Definition rl_lenf_mloop : list positive :=
    [ kA3; kS3; kA4 ].
  Definition rl_lenf_mafter : list positive :=
    [ kA3; kS3 ].
  Definition keep_lenf_mloop : list positive :=
    [ kSP; kGP; kTP; kS0; kA0; kA1; kRA; kT6; kT4; kS9; kS4; kS2; kS6; kS7; kS8; kS11; kA2 ].
  Definition L_M4C : Z := 93108.
  Definition L_M54 : Z := 93116.
  Definition L_M30 : Z := 93080.
  Definition L_M3C : Z := 93092.
  Definition s_regs_lenf_m : list (positive * quant) :=
    [ (kSP, Q_arg_at 0 (-224));
      (kGP, Q_arg 1);
      (kTP, Q_arg 2);
      (kS0, Q_arg 3);
      (kA0, Q_arg 0);
      (kA1, Q_lit 0);
      (kS6, Q_arg_at 3 168);
      (kT6, Q_lit (-16180));
      (kT4, Q_lit 30);
      (kS9, Q_lit JTAB_ADDR);
      (kS4, Q_lit 16209);
      (kS2, Q_arg 4);
      (kRA, Q_arg 5);
      (kS7, Q_arg 6);
      (kS8, Q_arg 7);
      (kS11, Q_arg 8);
      (kS3, Q_arg 9) ].
  Definition L_DLOOP1 : Z := 92452.
  Definition L_D04 : Z := 92524.
  Definition L_DLOOP2 : Z := 92612.
  Definition L_D8BC : Z := 92708.
  Definition L_DXLOOP : Z := 92824.
  Definition L_DX80 : Z := 92900.
  Definition L_LXLOOP : Z := 87140.
  Definition L_LX60 : Z := 89320.
  Definition L_LVX_L1 : Z := 93492.
  Definition L_LVX_L2 : Z := 93576.
  Definition L_LVX_EXT : Z := 93536.
  Definition keep_lenf_d1 : list positive :=
    [ kRA; kSP; kGP; kTP; kS0; kS1; kA0; kA1; kA5; kA7; kS2; kS3; kS4; kS6; kS8; kS9; kS11; kT3; kT4; kT6 ].
  Definition keep_lenf_d2 : list positive :=
    [ kRA; kSP; kGP; kTP; kS0; kA0; kA1; kA2; kA3; kA4; kA5; kA6; kS2; kS3; kS4; kS6; kS9; kS10; kS11 ].
  Definition keep_lenf_x : list positive :=
    [ kRA; kSP; kGP; kTP; kT0; kT1; kS0; kS1; kA0; kA1; kA3; kS2; kS3; kS4; kS6; kS8; kS9; kS10; kS11; kT3; kT4; kT6 ].
  Definition keep_lenf_l1 : list positive :=
    [ kRA; kSP; kGP; kTP; kT0; kT1; kT2; kS0; kA0; kA1; kA3; kA4; kA5; kA6; kA7; kS3; kS4; kS6; kS7; kS9; kS10; kT3; kT4; kT6 ].
  Definition keep_lenf_l2 : list positive :=
    [ kRA; kSP; kGP; kTP; kT0; kT1; kT2; kS0; kS1; kA0; kA1; kA3; kA4; kA5; kA6; kA7; kS3; kS4; kS6; kS7; kS9; kS10; kT3; kT4; kT6 ].
  Definition rl_lenf_d1 : list positive :=
    [ kA5; kA7; kA2; kT1; kT0; kA3; kS7; kA4; kA6; kS2; kS8; kS11 ].
  Definition rl_lenf_d1x : list positive :=
    [ kS7 ].
  Definition rl_lenf_d1d : list positive :=
    [ kS10; kA2; kA3; kT0; kS7; kA4; kA6 ].
  Definition rl_lenf_d2 : list positive :=
    [ kT1; kA4; kA6; kA5; kA2; kA3; kS10; kA7; kT6; kT4; kT0; kS7; kT3; kT2 ].
  Definition rl_lenf_d2x : list positive :=
    [ kS7 ].
  Definition rl_lenf_d2d : list positive :=
    [ kT5; kA7; kT0; kT4; kS7; kT3; kT2 ].
  Definition rl_lenf_x : list positive :=
    [ kA3; kA2; kA6; kA4; kS7; kS2; kS8; kS11 ].
  Definition rl_lenf_xx : list positive :=
    [ kS7 ].
  Definition rl_lenf_xd : list positive :=
    [ kA5; kA2; kA4; kS7 ].
  Definition s_regs_lenf_l1 : list (positive * quant) :=
    [ (kS2, Q_arg 0);
      (kS8, Q_arg 1);
      (kS11, Q_arg 2);
      (kSP, Q_arg_at 3 (-224)) ].
  Definition rl_lenf_l1k : list positive :=
    [ kS8; kS11; kS2; kS1 ].
  Definition rl_lenf_l2k : list positive :=
    [ kS8; kS11; kS2 ].
  Definition L_DX20 : Z := 92804.
  Definition L_DXBC : Z := 92960.
  Definition s_regs_lenf_xr : list (positive * quant) :=
    [ (kSP, Q_arg_at 0 (-224));
      (kGP, Q_arg 1);
      (kTP, Q_arg 2);
      (kS0, Q_arg 3);
      (kA0, Q_arg 0);
      (kA1, Q_lit 0);
      (kS6, Q_arg_at 3 168);
      (kT6, Q_lit (-16180));
      (kT4, Q_lit 30);
      (kS9, Q_lit JTAB_ADDR);
      (kS4, Q_lit 16209);
      (kS3, Q_arg 4);
      (kRA, Q_arg 5);
      (kS2, Q_arg 6);
      (kS8, Q_arg 7);
      (kS11, Q_arg 8) ].
  Definition rl_lenf_xh : list positive :=
    [ kS7 ].
  Definition rl_lenf_j80 : list positive :=
    [ kA5; kA2; kA4; kS7; kA3 ].
  Definition L_D8EC : Z := 92752.
  Definition L_DBAD : Z := 92864.
  Definition s_regs_lenf_dr : list (positive * quant) :=
    [ (kSP, Q_arg_at 0 (-224));
      (kGP, Q_arg 1);
      (kTP, Q_arg 2);
      (kS0, Q_arg 3);
      (kA0, Q_arg 0);
      (kA1, Q_lit 0);
      (kS6, Q_arg_at 3 168);
      (kS4, Q_lit 16209);
      (kS3, Q_arg 4);
      (kRA, Q_arg 5);
      (kS9, Q_lit 67008) ].
  Definition rl_lenf_j8ec : list positive :=
    [ kT6; kT4; kS9; kS2; kT1; kA6; kA4; kA3; kS7; kA5; kS10; kA2 ].
  Definition rl_lenf_kx1 : list positive :=
    [ kS7; kS2; kS8; kS11 ].
  Definition rl_lenf_j04 : list positive :=
    [ kT6; kT4; kS9; kS2; kS8; kS11; kA5; kA7; kS10; kA2; kA3; kS7; kA6; kA4 ].
  Definition rl_lenf_j8bc : list positive :=
    [ kS11; kA5; kA4; kA6; kS2; kA2; kA3; kS10; kT5; kA7; kT0; kS7; kT3; kT2 ].
  (* ---- PATCH: S_ZA-rows-entry-P.tsv md5 : 4 fields ---- *)
  Definition s_regs_za_entry : list (positive * quant) :=
    [ (kSP, Q_u_at (-32));
      (kS1, Q_u);
      (kA0, Q_p);
      (kS3, Q_arg 0);
      (kS4, Q_lit 262144);
      (kS5, Q_entry kS5);
      (kGP, Q_entry kGP);
      (kTP, Q_entry kTP);
      (kS6, Q_entry kS6);
      (kS7, Q_entry kS7);
      (kS8, Q_entry kS8);
      (kS9, Q_entry kS9);
      (kS10, Q_entry kS10);
      (kS11, Q_entry kS11) ].
  Definition f_za_entry : list fslot :=
    [ ("buf"%string, (-32), W8, Q_lit BUF);
      ("len"%string, (-24), W8, Q_u_at 160);
      ("left"%string, (-16), W8, Q_u_at 168);
      ("ra"%string, (-8), W8, Q_lit RA_II) ].
  Definition ZA_STK_LO : Z := (-1024).
  Definition ZA_STK_LEN : Z := 1232.
End L.
