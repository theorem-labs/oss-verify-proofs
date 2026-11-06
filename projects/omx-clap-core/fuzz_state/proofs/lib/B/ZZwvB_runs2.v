(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) twin of lib/A/ZZwv_runs2.v (a working branch
   1a5dc5b2e7c): same lemma names, every return address, frame slot and register re-measured on fs.asan-ubsan (B's loop
   registers: s5 = i in 21, s7 = 56 i in 23, s9 = 8 i in 25, s6 = d + 1 in 22, s10 = 0 in 26); the runs that meet a UBSan
   guard the engine cannot decide take its condition (ZZwvB_defs.wvc_cKIDS / wvc_cMULH / wvc_cI60 / wvc_cKEYS), proved
   from the segment's premises; imports point at lib/B's image files and walk kit.
   rule 24: proves no function (kind: segment lemma) - the container arms of write_value B. *)
(* The engine segments INSIDE write_value's container item loop (fs.asan-ubsan image B, write_value 0x84010), each one
   token run from a resume point `wvc_ssL ty p r` of ZZwvB_defs.v to the next call site, with the caller's journal and
   ARU carried through. No semantics, no function contract, no allocator reasoning.
   MEASURED with the engine on the pinned fs.asan-ubsan (a build machine, this lane's probe of these exact states, p = 0 and
   p = 1, ty = 5 and ty = 6): every run below ends TS_running at the callee's entry with sh_obls = [] and sh_j = 0 (so
   the token env extK E K [] is E again), the frame region at the stop still carries exactly wvc_csL p, and sp is
   unchanged except at the closing TAIL jump.
   Every proof splits on p as image A's does (with p symbolic the engine's run does not normalise; p <> 0 is p = 1
   for the whole resumed state, wvc_ssL_p1).
   The state's region list, atom facts and shadow list are by type (wvc_rsL / wvc_gfL / wvc_SHL: the object's key-slot
   region and shadow entry exist for ty = 6 only), so the segments shared by both arms take ty = 5 \/ ty = 6 and run
   once per literal type. wvc_seg_closeN is wvc_seg_close from the close-point state wvc_ssN ty p (the node alone for
   both arms, shadow list wvc_SH0): after the last item the key cursor may lie past the keys block.
   UBSan (trap `unimp` at 0x84444): the guards on these runs, and what rules each out, are named at each segment.
   FRAME TOP vs JOURNAL TOP: write_value's frame is [spF - WVC_F, spF) below its entry sp spF; the caller's journal
   carries a RAISED top sp0 >= spF and the stack bound STK, so every segment takes spF <= sp0 and
   sp0 - STK <= spF - WVC_F, and every continuation also hands over gp / tp (regs 3, 4), which the state never writes.
   Rule 24 (proof-index, a Theorem Labs lane 04:2xZ, unpiped): write_value has RELEASED proofs for fs's PLAIN and UBSAN
   builds only (lib/Prog, lib/U/Prog), none for an ASan image; 0x84010 is not in the released set. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_rres FSW_ret FSW_pj FSH_Fn_writer
FSW_write_value_entry ZZwvB_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================= p <> 0 is p = 1 for the whole resumed state ================= *)
Lemma wvc_sep_p1 : forall p, p <> 0 -> wvc_sep p = wvc_sep 1.
Proof. intros p Hp. unfold wvc_sep. rewrite (proj2 (Z.eqb_neq p 0) Hp). reflexivity. Qed.
Lemma wvc_seplen_p1 : forall p, p <> 0 -> wvc_seplen p = wvc_seplen 1.
Proof. intros p Hp. unfold wvc_seplen. rewrite (proj2 (Z.eqb_neq p 0) Hp). reflexivity. Qed.
Lemma wvc_csL_p1 : forall p, p <> 0 -> wvc_csL p = wvc_csL 1.
Proof.
intros p Hp. unfold wvc_csL. rewrite (wvc_sep_p1 p Hp), (wvc_seplen_p1 p Hp). reflexivity.
Qed.
Lemma wvc_ssL_p1 : forall ty p r, p <> 0 -> wvc_ssL ty p r = wvc_ssL ty 1 r.
Proof.
intros ty p r Hp. unfold wvc_ssL. rewrite (wvc_csL_p1 p Hp), (proj2 (Z.eqb_neq p 0) Hp). reflexivity.
Qed.
Lemma wvc_ssN_p1 : forall ty p, p <> 0 -> wvc_ssN ty p = wvc_ssN ty 1.
Proof.
intros ty p Hp. unfold wvc_ssN. rewrite (wvc_csL_p1 p Hp), (proj2 (Z.eqb_neq p 0) Hp). reflexivity.
Qed.
Lemma wvc_sep_range : forall p, 0 <= wvc_sep p < 2 ^ 64.
Proof. intros p. unfold wvc_sep, WVC_COLON, WVC_COLON_SP. destruct (p =? 0); lia. Qed.
Lemma wvc_seplen_range : forall p, 0 <= wvc_seplen p < 2 ^ 64.
Proof. intros p. unfold wvc_seplen. destruct (p =? 0); lia. Qed.
Lemma wvc_close_range : forall ty, 0 <= wvc_close ty < 2 ^ 64.
Proof. intros ty. unfold wvc_close, WVC_RBRACE, WVC_RBRACKET. destruct (ty =? 6); lia. Qed.

(* ================= the arithmetic of the registers the segments hand over ================= *)
Lemma wvc_u_atom : forall E m a, ew E m = Z_to_bv 64 a -> 0 <= a < 2 ^ 64 -> bv_unsigned (ew E m) = a.
Proof. intros E m a H Ha. rewrite H. apply unsigned_lit_small. exact Ha. Qed.

Lemma wvc_u_off : forall E m a z, ew E m = Z_to_bv 64 a -> 0 <= a < 2 ^ 64 -> 0 <= a + z < 2 ^ 64 ->
  U E (SOff m z) = a + z.
Proof.
intros E m a z H Ha Hz. rewrite U_SOff, (wvc_u_atom E m a H Ha). unfold zcanon, M64. apply Z.mod_small. exact Hz.
Qed.

Lemma wvc_u_add : forall E m1 m2 a b, ew E m1 = Z_to_bv 64 a -> ew E m2 = Z_to_bv 64 b ->
  0 <= a -> 0 <= b -> a + b < 2 ^ 64 -> U E (SAlu ALU_ADD (SOff m1 0) (SOff m2 0)) = a + b.
Proof.
intros E m1 m2 a b H1 H2 Ha Hb Hab.
rewrite U_SAlu, (wvc_u_off E m1 a 0 H1 ltac:(lia) ltac:(lia)), (wvc_u_off E m2 b 0 H2 ltac:(lia) ltac:(lia)).
cbn [zalu_raw]. unfold zcanon, M64. rewrite Z.mod_small by lia. lia.
Qed.

(* the 32-bit  d + 1  the arms pass as the callee's depth, sign-extended back to 64 bits *)
Lemma wvc_u_w1 : forall E m d, ew E m = Z_to_bv 64 d -> 0 <= d -> d + 1 < 2 ^ 31 ->
  U E (SAluw ALU_ADD (SOff m 0) (SLit 1)) = d + 1.
Proof.
intros E m d H Hd0 Hd1.
rewrite U_of_S, S_SAluw, (wvc_u_off E m d 0 H ltac:(lia) ltac:(lia)), U_SLit.
unfold zcanon, M64. rewrite (Z.mod_small 1 (2 ^ 64)) by lia.
rewrite (Z.mod_small (d + 0) (2 ^ 32)) by lia. rewrite (Z.mod_small 1 (2 ^ 32)) by lia.
cbn [zalu_raw]. rewrite (swrap32_id (d + 0 + 1)) by lia.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. lia.
Qed.

(* image B passes s6 = addiw d 1 by one `mv` (addi 0) *)
Lemma wvc_u_d1 : forall E m d, ew E m = Z_to_bv 64 d -> 0 <= d -> d + 1 < 2 ^ 31 ->
  U E (SAlu ALU_ADD (SAluw ALU_ADD (SOff m 0) (SLit 1)) (SLit 0)) = d + 1.
Proof.
intros E m d H Hd0 Hd1.
rewrite U_SAlu, (wvc_u_w1 E m d H Hd0 Hd1), U_SLit.
cbn [zalu_raw]. unfold zcanon, M64. rewrite (Z.mod_small 0 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

(* the loop's key cursor: (keys * -1 + 8) + (keys + 8 * i), which the engine keeps in this linear form *)
Lemma wvc_u_cursor : forall E m1 m2 keys ke,
  ew E m1 = Z_to_bv 64 keys -> ew E m2 = Z_to_bv 64 ke ->
  0 <= keys -> keys <= ke -> ke + 8 < 2 ^ 64 ->
  U E (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff m1 0) (SLit (-1))) (SLit 8)) (SOff m2 0))
    = ke + 8 - keys.
Proof.
intros E m1 m2 keys ke H1 H2 Hk Hke Hke8.
rewrite U_SAlu, U_SAlu, U_SMd, (wvc_u_off E m1 keys 0 H1 ltac:(lia) ltac:(lia)),
  (wvc_u_off E m2 ke 0 H2 ltac:(lia) ltac:(lia)), !U_SLit.
cbn [zalu_raw zmd_raw]. unfold zcanon, M64.
rewrite (Z.mod_small 8 (2 ^ 64)) by lia.
rewrite (Z.mul_mod_idemp_r (keys + 0) (-1) (2 ^ 64)) by lia.
rewrite !Z.add_mod_idemp_l by lia. rewrite <- Z.add_assoc.
rewrite Z.add_mod_idemp_l by lia.
replace ((keys + 0) * -1 + (8 + (ke + 0))) with (ke + 8 - keys) by lia.
apply Z.mod_small. lia.
Qed.

(* ---- the operands of the UBSan guards on the item's address: 56 i, its signed high half, its sign ---- *)
Lemma wvc_u_mul56 : forall E i, ew E 21 = Z_to_bv 64 i -> 0 <= i -> 56 * i < 2 ^ 63 ->
  U E (SMd M_MUL (SOff 21 0) (SLit 56)) = 56 * i.
Proof.
intros E i H Hi0 Hi.
rewrite U_SMd, (wvc_u_off E 21 i 0 H ltac:(lia) ltac:(lia)), U_SLit. cbn [zmd_raw].
change (zcanon 56) with 56. rewrite Z.add_0_r. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma wvc_u_mulh56 : forall E i, ew E 21 = Z_to_bv 64 i -> 0 <= i -> 56 * i < 2 ^ 63 ->
  U E (SMd M_MULH (SOff 21 0) (SLit 56)) = 0.
Proof.
intros E i H Hi0 Hi.
rewrite U_SMd, (wvc_u_off E 21 i 0 H ltac:(lia) ltac:(lia)), U_SLit. cbn [zmd_raw].
change (zcanon 56) with 56. try change (Z.of_N 64) with 64. rewrite Z.add_0_r.
rewrite (swrap64_id i), (swrap64_id 56) by (unfold half64; lia).
rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
Qed.
Lemma wvc_u_sra56 : forall E i, ew E 21 = Z_to_bv 64 i -> 0 <= i -> 56 * i < 2 ^ 63 ->
  U E (SAlu ALU_SRA (SMd M_MUL (SOff 21 0) (SLit 56)) (SLit 63)) = 0.
Proof.
intros E i H Hi0 Hi.
rewrite U_SAlu, (wvc_u_mul56 E i H Hi0 Hi), U_SLit. cbn [zalu_raw].
change (zcanon 63) with 63. change (Z.land 63 63) with 63.
rewrite (swrap64_id (56 * i)) by (unfold half64; lia).
rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

Section C. Context {fx : YK11.FPState}.
(* ---- the guard conditions, added to a state from the segment's premises ---- *)
(* 0x84250 `bltu (56 i + kids) kids` *)
Lemma wvc_add_cKIDS : forall E ss ms i kids, st_ok tfibsegs E ss ms ->
  ew E 21 = Z_to_bv 64 i -> ew E (xatom 1) = Z_to_bv 64 kids -> 0 <= i -> 0 <= kids -> kids + 56 * i < 2 ^ 63 ->
  st_ok tfibsegs E (add_cond ss wvc_cKIDS) ms.
Proof.
intros E ss ms i kids HS H21 Hk Hi0 Hk0 Hki. unfold wvc_cKIDS. apply st_ok_add_cond; [exact HS|].
rewrite branch_geu_U, U_SAlu, (wvc_u_mul56 E i H21 Hi0 ltac:(lia)),
  (wvc_u_off E (xatom 1) kids 0 Hk ltac:(lia) ltac:(lia)).
cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia). apply negb_true_iff, Z.ltb_ge. lia.
Qed.
(* 0x84268 `bnez (snez (mulh i 56 ^ (56 i >>s 63)))` *)
Lemma wvc_add_cMULH : forall E ss ms i, st_ok tfibsegs E ss ms ->
  ew E 21 = Z_to_bv 64 i -> 0 <= i -> 56 * i < 2 ^ 63 ->
  st_ok tfibsegs E (add_cond ss wvc_cMULH) ms.
Proof.
intros E ss ms i HS H Hi0 Hi. unfold wvc_cMULH. apply st_ok_add_cond; [exact HS|].
rewrite branch_eq_U, U_SLit, U_SAlu, U_SLit, U_SAlu, (wvc_u_mulh56 E i H Hi0 Hi), (wvc_u_sra56 E i H Hi0 Hi).
vm_compute. reflexivity.
Qed.
(* 0x841e0 `bnez (srli s5 60)` *)
Lemma wvc_add_cI60 : forall E ss ms i, st_ok tfibsegs E ss ms ->
  ew E 21 = Z_to_bv 64 i -> 0 <= i < 2 ^ 54 -> st_ok tfibsegs E (add_cond ss wvc_cI60) ms.
Proof.
intros E ss ms i HS H Hi. unfold wvc_cI60. apply st_ok_add_cond; [exact HS|].
rewrite branch_eq_U, U_SAlu, !U_SLit, (wvc_u_off E 21 i 0 H ltac:(lia) ltac:(lia)). cbn [zalu_raw].
change (zcanon 60) with 60. change (Z.land 60 63) with 60. rewrite Z.add_0_r.
rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. vm_compute. reflexivity.
Qed.
(* 0x841e4 `bltu (keys + 8 i) keys` *)
Lemma wvc_add_cKEYS : forall E ss ms keys i, st_ok tfibsegs E ss ms ->
  ew E (xatom 18) = Z_to_bv 64 (keys + 8 * i) -> ew E (xatom 2) = Z_to_bv 64 keys ->
  0 <= keys -> 0 <= i -> keys + 8 * i < 2 ^ 64 -> st_ok tfibsegs E (add_cond ss wvc_cKEYS) ms.
Proof.
intros E ss ms keys i HS H18 H2 Hk Hi Hb. unfold wvc_cKEYS. apply st_ok_add_cond; [exact HS|].
rewrite branch_geu_U, (wvc_u_off E (xatom 18) (keys + 8 * i) 0 H18 ltac:(lia) ltac:(lia)),
  (wvc_u_off E (xatom 2) keys 0 H2 ltac:(lia) ltac:(lia)).
apply negb_true_iff, Z.ltb_ge. lia.
Qed.
End C.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.

(* ---- what each run must show of its own writes: only write_value's frame [spF - WVC_F, spF), which lies inside the
   caller's journal window [sp0 - STK, sp0) ---- *)
Lemma wvc_awrL : forall E ty p r STK sp0 spF FP bl0 blc lyc own fr0,
  bv_unsigned (ew E 2) = spF - WVC_F -> spF <= sp0 -> sp0 - STK <= spF - WVC_F ->
  awr_ok tfibsegs B E (ss_mem (wvc_ssL ty p r)) STK sp0 FP bl0 blc lyc own fr0.
Proof.
intros E ty p r STK sp0 spF FP bl0 blc lyc own fr0 E2 Hsp HSTK.
unfold wvc_ssL, wvc_setr, fss_retT, fsT_ret_regions, wvc_rsL.
destruct (ty =? 6); cbn [add_cond ss_mem app].
all: eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spF - WVC_F - sp0);
  [ reflexivity
  | rewrite E2; lia
  | cbv [fstk_ret YP09.r_wlo]; unfold WVC_F in *; lia
  | cbv [fstk_ret YP09.r_whi]; unfold WVC_F in *; lia
  | ].
all: apply awr_ok_cons_ro; [cbv [fs_got_region YP09.r_wlo YP09.r_whi]; lia|].
all: apply awr_ok_cons_ro; [cbv [fs_bcell_region YP09.r_wlo YP09.r_whi]; lia|].
all: apply awr_ok_cons_ro; [cbv [wvc_node YP09.r_wlo YP09.r_whi]; lia|].
- apply awr_ok_cons_ro; [cbv [wvc_keyR YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_nil.
- apply awr_ok_nil.
Qed.
Lemma wvc_awrN : forall E ty p STK sp0 spF FP bl0 blc lyc own fr0,
  bv_unsigned (ew E 2) = spF - WVC_F -> spF <= sp0 -> sp0 - STK <= spF - WVC_F ->
  awr_ok tfibsegs B E (ss_mem (wvc_ssN ty p)) STK sp0 FP bl0 blc lyc own fr0.
Proof.
intros E ty p STK sp0 spF FP bl0 blc lyc own fr0 E2 Hsp HSTK.
unfold wvc_ssN, wvc_setr, fss_retT, fsT_ret_regions. cbn [add_cond ss_mem app].
eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spF - WVC_F - sp0);
  [ reflexivity
  | rewrite E2; lia
  | cbv [fstk_ret YP09.r_wlo]; unfold WVC_F in *; lia
  | cbv [fstk_ret YP09.r_whi]; unfold WVC_F in *; lia
  | ].
apply awr_ok_cons_ro; [cbv [fs_got_region YP09.r_wlo YP09.r_whi]; lia|].
apply awr_ok_cons_ro; [cbv [fs_bcell_region YP09.r_wlo YP09.r_whi]; lia|].
apply awr_ok_cons_ro; [cbv [wvc_node YP09.r_wlo YP09.r_whi]; lia|].
apply awr_ok_nil.
Qed.

(* ---- the bytes the run kept: everything outside write_value's own frame ---- *)
Lemma wvc_outL : forall E ty p r (m m' : word -> option byte) sp0,
  frame_of E (ss_mem (wvc_ssL ty p r)) m m' -> bv_unsigned (ew E 2) = sp0 - WVC_F ->
  forall x : word, ~ (sp0 - WVC_F <= bv_unsigned x < sp0) -> m' x = m x.
Proof.
intros E ty p r m m' sp0 HF E2 x Hx. apply HF. intros (rg & Hin & Hr).
unfold wvc_ssL, wvc_setr, fss_retT, fsT_ret_regions, wvc_rsL in Hin.
destruct (ty =? 6); cbn [add_cond ss_mem app In] in Hin.
- destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]];
    cbv [fstk_ret fs_got_region fs_bcell_region wvc_node wvc_keyR
         YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    try rewrite E2 in Hr; unfold WVC_F in *; lia.
- destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
    cbv [fstk_ret fs_got_region fs_bcell_region wvc_node
         YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    try rewrite E2 in Hr; unfold WVC_F in *; lia.
Qed.
Lemma wvc_outN : forall E ty p (m m' : word -> option byte) sp0,
  frame_of E (ss_mem (wvc_ssN ty p)) m m' -> bv_unsigned (ew E 2) = sp0 - WVC_F ->
  forall x : word, ~ (sp0 - WVC_F <= bv_unsigned x < sp0) -> m' x = m x.
Proof.
intros E ty p m m' sp0 HF E2 x Hx. apply HF. intros (rg & Hin & Hr).
unfold wvc_ssN, wvc_setr, fss_retT, fsT_ret_regions in Hin. cbn [add_cond ss_mem app In] in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
  cbv [fstk_ret fs_got_region fs_bcell_region wvc_node
       YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
  try rewrite E2 in Hr; unfold WVC_F in *; lia.
Qed.

(* ---- the frame slots the next resume will read back, on the memory at the call ---- *)
Lemma wvc_chunksL : forall (W : world tfibsegs) E ss ms p sp0,
  st_ok tfibsegs E ss (restrict (w_H W) ms) ->
  nth_error (ss_mem ss) 0%nat = Some (fstk_ret WVC_F (wvc_csL p)) ->
  bv_unsigned (ew E 2) = sp0 - WVC_F ->
  Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W) (ms_mem ms)) (sp0 - WVC_F)) (wvc_csL p).
Proof.
intros W E ss ms p sp0 HS Hn E2.
pose proof (fsw_region_nth E ss (restrict (w_H W) ms) 0%nat _ HS Hn) as (_ & _ & _ & HCH).
cbv [fstk_ret] in HCH. cbn [YP09.r_base YP09.r_chunks base_val] in HCH. rewrite E2 in HCH. exact HCH.
Qed.

(* ---- reading one register of the state the run reached ---- *)
Lemma wvc_regE : forall (W : world tfibsegs) E ss ms (q : bv 5) m,
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> sr_get (ss_regs ss) q = SOff m 0 ->
  YK11.getr (ms_regs ms) q = ew E m.
Proof.
intros W E ss ms q m HS Hq. rewrite (st_ok_restrict_reg tfibsegs (w_H W) E ss ms q HS), Hq. apply fsw_SOff0.
Qed.

Lemma wvc_regU : forall (W : world tfibsegs) E ss ms (q : bv 5) e c,
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> sr_get (ss_regs ss) q = e -> U E e = c ->
  YK11.getr (ms_regs ms) q = w64 c.
Proof.
intros W E ss ms q e c HS Hq HU.
rewrite (st_ok_restrict_reg tfibsegs (w_H W) E ss ms q HS), Hq, denot_lit_U, HU. reflexivity.
Qed.

Lemma wvc_regL : forall (W : world tfibsegs) E ss ms (q : bv 5) z,
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> sr_get (ss_regs ss) q = SLit z -> 0 <= z < 2 ^ 64 ->
  YK11.getr (ms_regs ms) q = w64 z.
Proof. intros W E ss ms q z HS Hq Hz. exact (fsw_reg_lit (w_H W) E ss ms q z HS Hq Hz). Qed.

(* ---- the steps every segment's tail repeats (the run's st_ok and RSTART found by their form) ---- *)
Ltac wvc_shape :=
  lazymatch goal with HSx : st_ok _ _ _ (restrict _ _) |- _ =>
    let HSH := fresh "HSH" in
    pose proof (st_ok_restrict_mkst tfibsegs _ _ _ _ HSx) as HSH; apply HSH; vm_compute; reflexivity
  end.
Ltac wvc_same E W :=
  (lazymatch goal with HSx : st_ok _ _ ?ssf (restrict _ _) |- _ =>
     rewrite (st_ok_restrict_reg tfibsegs (w_H W) E ssf _ _ HSx) end);
  (lazymatch goal with RS : forall q : bv 5, YK11.getr _ q = _ |- _ => rewrite RS end);
  f_equal; vm_compute; reflexivity.
Ltac wvc_keep E W :=
  let q := fresh "q" in let Hq := fresh "Hq" in
  intros q Hq; cbv [In] in Hq; repeat (destruct Hq as [<-|Hq]); [..|destruct Hq];
  wvc_same E W.

(* ================= (1) the array arm's per-item indent returned: call write_value ================= *)
(* UBSan guards on this run: 0x8424c (`beq (snez kids) (seqz (56 i + kids))`) the engine decides from wvc_gfA (kids =
   xatom 1 >= 4096, i = atom 21 < 2 ^ 54); 0x84250 (`bltu (56 i + kids) kids`) is ruled out by wvc_cKIDS, from
   kids + 56 * n <= alloc_ceiling and i < n; 0x84268 (the signed overflow of 56 i, mulh) by wvc_cMULH, from
   i < n <= 2 ^ 54. *)
Lemma wvc_seg_ind_arr : forall (W : world tfibsegs) ms mdc E p i n d kids
    STK sp0 spF FP ly S W0 mem md own lyc Sc U k (Q : world tfibsegs -> config -> Prop),
  wvc_at B E (wvc_ssL 5 p WVC_R_IND) (wvc_SHL 5) W ms STK sp0 FP ly S W0 mem md own lyc Sc U mdc k ->
  ew E 21 = Z_to_bv 64 i -> ew E 23 = Z_to_bv 64 (56 * i) -> ew E (xatom 1) = Z_to_bv 64 kids ->
  ew E (xatom 4) = Z_to_bv 64 d ->
  0 <= i < n -> n <= 2 ^ 54 -> 0 <= kids -> kids + 56 * n <= alloc_ceiling ->
  0 <= d -> d + 1 < 2 ^ 31 ->
  bv_unsigned (ew E 2) = spF - WVC_F -> spF <= sp0 -> sp0 - STK <= spF - WVC_F ->
  (forall ms' mdc',
     ms' = mkst (ms_regs ms') (w64 A_write_value) (ms_mem ms') (seg_rom tfibsegs) ->
     ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U (ms_mem ms')) mdc' k ->
     ARU tfibsegs B lyc Sc U W (ms_mem ms') mdc' ->
     (forall x : word, ~ (spF - WVC_F <= bv_unsigned x < spF) ->
        mrestrict (w_H W) (ms_mem ms') x = mrestrict (w_H W) (ms_mem ms) x) ->
     Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W) (ms_mem ms')) (spF - WVC_F)) (wvc_csL p) ->
     YK11.getr (ms_regs ms') 1%bv = w64 WVC_R_ITEM ->
     YK11.getr (ms_regs ms') 10%bv = ew E 8 ->
     YK11.getr (ms_regs ms') 11%bv = w64 (kids + 56 * i) ->
     YK11.getr (ms_regs ms') 12%bv = ew E 19 ->
     YK11.getr (ms_regs ms') 13%bv = w64 (d + 1) ->
     YK11.getr (ms_regs ms') 2%bv = YK11.getr (ms_regs ms) 2%bv ->
     (forall q, In q [3;4;8;9;18;19;20;21;22;23;24;25;26;27]%bv ->
        YK11.getr (ms_regs ms') q = YK11.getr (ms_regs ms) q) ->
     SRr tfibsegs W (mkCfg ms' mdc') Q) ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros W ms mdc E p i n d kids STK sp0 spF FP ly S W0 mem md own lyc Sc U k Q
  (HS0 & SHOK & HJ & HARU) H21 H23 H34 H37 Hin Hn Hk0 Hkn Hd0 Hd1 E2 Hsp HSTK HQ.
pose proof asan_consts as (HC1 & _).
assert (RSTART : forall q : bv 5,
  YK11.getr (ms_regs ms) q = sv_denot E (sr_get (ss_regs (wvc_ssL 5 p WVC_R_IND)) q))
  by (intros q; exact (st_ok_restrict_reg tfibsegs (w_H W) E _ ms q HS0)).
assert (HS : st_ok tfibsegs E (add_cond (add_cond (wvc_ssL 5 p WVC_R_IND) wvc_cKIDS) wvc_cMULH)
  (restrict (w_H W) ms)).
{ apply (wvc_add_cMULH E _ _ i); [| exact H21 | lia | lia].
  apply (wvc_add_cKIDS E _ _ i kids HS0 H21 H34); lia. }
clear HS0.
destruct (Z.eq_dec p 0) as [->|Hp];
  [ idtac
  | rewrite (wvc_ssL_p1 5 p WVC_R_IND Hp) in HS, RSTART; rewrite (wvc_csL_p1 p Hp) in HQ ].
all: fsw_aj_run_to_tokU fsw_wr_tbl_ok HS HJ HARU SHOK fs_Bspan A_write_value;
  [ eapply wvc_awrL; [exact E2 | exact Hsp | exact HSTK]
  | apply HQ;
    [ wvc_shape
    | exact HJ
    | exact HARU
    | intros x Hx; cbn [add_cond ss_mem] in HFr; exact (wvc_outL _ _ _ _ _ _ _ HFr E2 x Hx)
    | eapply wvc_chunksL; [exact HS | vm_compute; reflexivity | exact E2]
    | eapply wvc_regL; [exact HS | vm_compute; reflexivity | unfold WVC_R_ITEM; lia]
    | eapply wvc_regE; [exact HS | vm_compute; reflexivity]
    | eapply (wvc_regU _ _ _ _ 11%bv (SAlu ALU_ADD (SOff 23 0) (SOff (xatom 1) 0)));
      [ exact HS | vm_compute; reflexivity
      | rewrite (wvc_u_add E 23 (xatom 1) (56 * i) kids H23 H34 ltac:(lia) ltac:(lia) ltac:(lia)); lia ]
    | eapply wvc_regE; [exact HS | vm_compute; reflexivity]
    | eapply (wvc_regU _ _ _ _ 13%bv (SAlu ALU_ADD (SAluw ALU_ADD (SOff (xatom 4) 0) (SLit 1)) (SLit 0)));
      [ exact HS | vm_compute; reflexivity | exact (wvc_u_d1 E (xatom 4) d H37 Hd0 Hd1) ]
    | wvc_same E W
    | wvc_keep E W ] ].
Qed.

(* ================= (2) the object arm's per-item indent returned: call put_string of the key ================= *)
(* UBSan guards on this run: 0x841d8 (`beq (snez keys) (seqz (keys + 8 i))`), 0x841e8 (`beqz keys`) and 0x841f4 (the
   key slot's alignment) the engine decides from wvc_gfK (keys = xatom 2 >= 4096, the slot xatom 18 >= 4096 and
   8-aligned); 0x841e0 (`bnez (srli i 60)`) is ruled out by wvc_cI60, from i < n <= 2 ^ 54; 0x841e4
   (`bltu (keys + 8 i) keys`) by wvc_cKEYS, from keys + 8 * n <= alloc_ceiling and i < n. *)
Lemma wvc_seg_ind_obj : forall (W : world tfibsegs) ms mdc E p i n keys
    STK sp0 spF FP ly S W0 mem md own lyc Sc U k (Q : world tfibsegs -> config -> Prop),
  wvc_at B E (wvc_ssL 6 p WVC_R_IND) (wvc_SHL 6) W ms STK sp0 FP ly S W0 mem md own lyc Sc U mdc k ->
  ew E 21 = Z_to_bv 64 i -> ew E (xatom 2) = Z_to_bv 64 keys -> ew E (xatom 18) = Z_to_bv 64 (keys + 8 * i) ->
  0 <= i < n -> n <= 2 ^ 54 -> 0 <= keys -> keys + 8 * n <= alloc_ceiling ->
  bv_unsigned (ew E 2) = spF - WVC_F -> spF <= sp0 -> sp0 - STK <= spF - WVC_F ->
  (forall ms' mdc',
     ms' = mkst (ms_regs ms') (w64 A_put_string) (ms_mem ms') (seg_rom tfibsegs) ->
     ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U (ms_mem ms')) mdc' k ->
     ARU tfibsegs B lyc Sc U W (ms_mem ms') mdc' ->
     (forall x : word, ~ (spF - WVC_F <= bv_unsigned x < spF) ->
        mrestrict (w_H W) (ms_mem ms') x = mrestrict (w_H W) (ms_mem ms) x) ->
     Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W) (ms_mem ms')) (spF - WVC_F)) (wvc_csL p) ->
     YK11.getr (ms_regs ms') 1%bv = w64 WVC_R_KEY ->
     YK11.getr (ms_regs ms') 10%bv = ew E 8 ->
     YK11.getr (ms_regs ms') 11%bv = ew E (xatom 19) ->
     YK11.getr (ms_regs ms') 2%bv = YK11.getr (ms_regs ms) 2%bv ->
     (forall q, In q [3;4;8;9;18;19;20;21;22;23;24;25;26;27]%bv ->
        YK11.getr (ms_regs ms') q = YK11.getr (ms_regs ms) q) ->
     SRr tfibsegs W (mkCfg ms' mdc') Q) ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros W ms mdc E p i n keys STK sp0 spF FP ly S W0 mem md own lyc Sc U k Q
  (HS0 & SHOK & HJ & HARU) H21 H35 H51 Hin Hn Hk0 Hkn E2 Hsp HSTK HQ.
pose proof asan_consts as (HC1 & _).
assert (RSTART : forall q : bv 5,
  YK11.getr (ms_regs ms) q = sv_denot E (sr_get (ss_regs (wvc_ssL 6 p WVC_R_IND)) q))
  by (intros q; exact (st_ok_restrict_reg tfibsegs (w_H W) E _ ms q HS0)).
assert (HS : st_ok tfibsegs E (add_cond (add_cond (wvc_ssL 6 p WVC_R_IND) wvc_cI60) wvc_cKEYS)
  (restrict (w_H W) ms)).
{ apply (wvc_add_cKEYS E _ _ keys i); [| exact H51 | exact H35 | lia | lia | lia].
  apply (wvc_add_cI60 E _ _ i HS0 H21); lia. }
clear HS0.
destruct (Z.eq_dec p 0) as [->|Hp];
  [ idtac
  | rewrite (wvc_ssL_p1 6 p WVC_R_IND Hp) in HS, RSTART; rewrite (wvc_csL_p1 p Hp) in HQ ].
all: fsw_aj_run_to_tokU fsw_wr_tbl_ok HS HJ HARU SHOK fs_Bspan A_put_string;
  [ eapply wvc_awrL; [exact E2 | exact Hsp | exact HSTK]
  | apply HQ;
    [ wvc_shape
    | exact HJ
    | exact HARU
    | intros x Hx; cbn [add_cond ss_mem] in HFr; exact (wvc_outL _ _ _ _ _ _ _ HFr E2 x Hx)
    | eapply wvc_chunksL; [exact HS | vm_compute; reflexivity | exact E2]
    | eapply wvc_regL; [exact HS | vm_compute; reflexivity | unfold WVC_R_KEY; lia]
    | eapply wvc_regE; [exact HS | vm_compute; reflexivity]
    | eapply wvc_regE; [exact HS | vm_compute; reflexivity]
    | wvc_same E W
    | wvc_keep E W ] ].
Qed.

(* ================= (3) the key's put_string returned: call put of the separator ================= *)
(* No UBSan guard is on this run. *)
Lemma wvc_seg_key : forall (W : world tfibsegs) ms mdc E p
    STK sp0 spF FP ly S W0 mem md own lyc Sc U k (Q : world tfibsegs -> config -> Prop),
  wvc_at B E (wvc_ssL 6 p WVC_R_KEY) (wvc_SHL 6) W ms STK sp0 FP ly S W0 mem md own lyc Sc U mdc k ->
  bv_unsigned (ew E 2) = spF - WVC_F -> spF <= sp0 -> sp0 - STK <= spF - WVC_F ->
  (forall ms' mdc',
     ms' = mkst (ms_regs ms') (w64 A_put) (ms_mem ms') (seg_rom tfibsegs) ->
     ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U (ms_mem ms')) mdc' k ->
     ARU tfibsegs B lyc Sc U W (ms_mem ms') mdc' ->
     (forall x : word, ~ (spF - WVC_F <= bv_unsigned x < spF) ->
        mrestrict (w_H W) (ms_mem ms') x = mrestrict (w_H W) (ms_mem ms) x) ->
     Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W) (ms_mem ms')) (spF - WVC_F)) (wvc_csL p) ->
     YK11.getr (ms_regs ms') 1%bv = w64 WVC_R_SEP ->
     YK11.getr (ms_regs ms') 10%bv = ew E 8 ->
     YK11.getr (ms_regs ms') 11%bv = w64 (wvc_sep p) ->
     YK11.getr (ms_regs ms') 12%bv = w64 (wvc_seplen p) ->
     YK11.getr (ms_regs ms') 2%bv = YK11.getr (ms_regs ms) 2%bv ->
     (forall q, In q [3;4;8;9;18;19;20;21;22;23;24;25;26;27]%bv ->
        YK11.getr (ms_regs ms') q = YK11.getr (ms_regs ms) q) ->
     SRr tfibsegs W (mkCfg ms' mdc') Q) ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros W ms mdc E p STK sp0 spF FP ly S W0 mem md own lyc Sc U k Q
  (HS & SHOK & HJ & HARU) E2 Hsp HSTK HQ.
assert (RSTART : forall q : bv 5,
  YK11.getr (ms_regs ms) q = sv_denot E (sr_get (ss_regs (wvc_ssL 6 p WVC_R_KEY)) q))
  by (intros q; exact (st_ok_restrict_reg tfibsegs (w_H W) E _ ms q HS)).
destruct (Z.eq_dec p 0) as [->|Hp];
  [ idtac
  | rewrite (wvc_ssL_p1 6 p WVC_R_KEY Hp) in HS, RSTART;
    rewrite (wvc_csL_p1 p Hp), (wvc_sep_p1 p Hp), (wvc_seplen_p1 p Hp) in HQ ].
all: fsw_aj_run_to_tokU fsw_wr_tbl_ok HS HJ HARU SHOK fs_Bspan A_put;
  [ eapply wvc_awrL; [exact E2 | exact Hsp | exact HSTK]
  | apply HQ;
    [ wvc_shape
    | exact HJ
    | exact HARU
    | intros x Hx; exact (wvc_outL _ _ _ _ _ _ _ HFr E2 x Hx)
    | eapply wvc_chunksL; [exact HS | vm_compute; reflexivity | exact E2]
    | eapply wvc_regL; [exact HS | vm_compute; reflexivity | unfold WVC_R_SEP; lia]
    | eapply wvc_regE; [exact HS | vm_compute; reflexivity]
    | eapply wvc_regL; [exact HS | vm_compute; reflexivity | apply wvc_sep_range]
    | eapply wvc_regL; [exact HS | vm_compute; reflexivity | apply wvc_seplen_range]
    | wvc_same E W
    | wvc_keep E W ] ].
Qed.

(* ================= (4) the separator's put returned: call write_value of the item ================= *)
(* UBSan guards on this run: as on (1), 0x8424c decided from wvc_gfA; 0x84250 ruled out by wvc_cKIDS (kids + 56 * n <=
   alloc_ceiling, i < n); 0x84268 by wvc_cMULH (i < n <= 2 ^ 54). *)
Lemma wvc_seg_sep : forall (W : world tfibsegs) ms mdc E p i n d kids
    STK sp0 spF FP ly S W0 mem md own lyc Sc U k (Q : world tfibsegs -> config -> Prop),
  wvc_at B E (wvc_ssL 6 p WVC_R_SEP) (wvc_SHL 6) W ms STK sp0 FP ly S W0 mem md own lyc Sc U mdc k ->
  ew E 21 = Z_to_bv 64 i -> ew E 23 = Z_to_bv 64 (56 * i) -> ew E (xatom 1) = Z_to_bv 64 kids ->
  ew E (xatom 4) = Z_to_bv 64 d ->
  0 <= i < n -> n <= 2 ^ 54 -> 0 <= kids -> kids + 56 * n <= alloc_ceiling ->
  0 <= d -> d + 1 < 2 ^ 31 ->
  bv_unsigned (ew E 2) = spF - WVC_F -> spF <= sp0 -> sp0 - STK <= spF - WVC_F ->
  (forall ms' mdc',
     ms' = mkst (ms_regs ms') (w64 A_write_value) (ms_mem ms') (seg_rom tfibsegs) ->
     ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U (ms_mem ms')) mdc' k ->
     ARU tfibsegs B lyc Sc U W (ms_mem ms') mdc' ->
     (forall x : word, ~ (spF - WVC_F <= bv_unsigned x < spF) ->
        mrestrict (w_H W) (ms_mem ms') x = mrestrict (w_H W) (ms_mem ms) x) ->
     Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W) (ms_mem ms')) (spF - WVC_F)) (wvc_csL p) ->
     YK11.getr (ms_regs ms') 1%bv = w64 WVC_R_ITEM ->
     YK11.getr (ms_regs ms') 10%bv = ew E 8 ->
     YK11.getr (ms_regs ms') 11%bv = w64 (kids + 56 * i) ->
     YK11.getr (ms_regs ms') 12%bv = ew E 19 ->
     YK11.getr (ms_regs ms') 13%bv = w64 (d + 1) ->
     YK11.getr (ms_regs ms') 2%bv = YK11.getr (ms_regs ms) 2%bv ->
     (forall q, In q [3;4;8;9;18;19;20;21;22;23;24;25;26;27]%bv ->
        YK11.getr (ms_regs ms') q = YK11.getr (ms_regs ms) q) ->
     SRr tfibsegs W (mkCfg ms' mdc') Q) ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros W ms mdc E p i n d kids STK sp0 spF FP ly S W0 mem md own lyc Sc U k Q
  (HS0 & SHOK & HJ & HARU) H21 H23 H34 H37 Hin Hn Hk0 Hkn Hd0 Hd1 E2 Hsp HSTK HQ.
pose proof asan_consts as (HC1 & _).
assert (RSTART : forall q : bv 5,
  YK11.getr (ms_regs ms) q = sv_denot E (sr_get (ss_regs (wvc_ssL 6 p WVC_R_SEP)) q))
  by (intros q; exact (st_ok_restrict_reg tfibsegs (w_H W) E _ ms q HS0)).
assert (HS : st_ok tfibsegs E (add_cond (add_cond (wvc_ssL 6 p WVC_R_SEP) wvc_cKIDS) wvc_cMULH)
  (restrict (w_H W) ms)).
{ apply (wvc_add_cMULH E _ _ i); [| exact H21 | lia | lia].
  apply (wvc_add_cKIDS E _ _ i kids HS0 H21 H34); lia. }
clear HS0.
destruct (Z.eq_dec p 0) as [->|Hp];
  [ idtac
  | rewrite (wvc_ssL_p1 6 p WVC_R_SEP Hp) in HS, RSTART; rewrite (wvc_csL_p1 p Hp) in HQ ].
all: fsw_aj_run_to_tokU fsw_wr_tbl_ok HS HJ HARU SHOK fs_Bspan A_write_value;
  [ eapply wvc_awrL; [exact E2 | exact Hsp | exact HSTK]
  | apply HQ;
    [ wvc_shape
    | exact HJ
    | exact HARU
    | intros x Hx; cbn [add_cond ss_mem] in HFr; exact (wvc_outL _ _ _ _ _ _ _ HFr E2 x Hx)
    | eapply wvc_chunksL; [exact HS | vm_compute; reflexivity | exact E2]
    | eapply wvc_regL; [exact HS | vm_compute; reflexivity | unfold WVC_R_ITEM; lia]
    | eapply wvc_regE; [exact HS | vm_compute; reflexivity]
    | eapply (wvc_regU _ _ _ _ 11%bv (SAlu ALU_ADD (SOff 23 0) (SOff (xatom 1) 0)));
      [ exact HS | vm_compute; reflexivity
      | rewrite (wvc_u_add E 23 (xatom 1) (56 * i) kids H23 H34 ltac:(lia) ltac:(lia) ltac:(lia)); lia ]
    | eapply wvc_regE; [exact HS | vm_compute; reflexivity]
    | eapply (wvc_regU _ _ _ _ 13%bv (SAlu ALU_ADD (SAluw ALU_ADD (SOff (xatom 4) 0) (SLit 1)) (SLit 0)));
      [ exact HS | vm_compute; reflexivity | exact (wvc_u_d1 E (xatom 4) d H37 Hd0 Hd1) ]
    | wvc_same E W
    | wvc_keep E W ] ].
Qed.

(* ================= (5) the item's write_value returned, another item follows: call put of the comma ========= *)
(* No UBSan guard is on this run (the loop test `bltu s5 n` at 0x84298 and `beqz s5` at 0x84178 take A's loop
   conditions). *)
Lemma wvc_seg_item_next : forall (W : world tfibsegs) ms mdc E ty p i n keys
    STK sp0 spF FP ly S W0 mem md own lyc Sc U k (Q : world tfibsegs -> config -> Prop),
  wvc_at B E (wvc_ssL ty p WVC_R_ITEM) (wvc_SHL ty) W ms STK sp0 FP ly S W0 mem md own lyc Sc U mdc k ->
  ty = 5 \/ ty = 6 ->
  ew E 21 = Z_to_bv 64 i -> ew E 23 = Z_to_bv 64 (56 * i) ->
  ew E (xatom 2) = Z_to_bv 64 keys -> ew E (xatom 3) = Z_to_bv 64 n ->
  ew E (xatom 18) = Z_to_bv 64 (keys + 8 * i) ->
  0 <= i -> i + 1 < n -> n <= 2 ^ 54 -> 0 <= keys -> keys + 8 * n <= alloc_ceiling ->
  bv_unsigned (ew E 2) = spF - WVC_F -> spF <= sp0 -> sp0 - STK <= spF - WVC_F ->
  (forall ms' mdc',
     ms' = mkst (ms_regs ms') (w64 A_put) (ms_mem ms') (seg_rom tfibsegs) ->
     ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U (ms_mem ms')) mdc' k ->
     ARU tfibsegs B lyc Sc U W (ms_mem ms') mdc' ->
     (forall x : word, ~ (spF - WVC_F <= bv_unsigned x < spF) ->
        mrestrict (w_H W) (ms_mem ms') x = mrestrict (w_H W) (ms_mem ms) x) ->
     Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W) (ms_mem ms')) (spF - WVC_F)) (wvc_csL p) ->
     YK11.getr (ms_regs ms') 1%bv = w64 WVC_R_COMMA ->
     YK11.getr (ms_regs ms') 10%bv = ew E 8 ->
     YK11.getr (ms_regs ms') 11%bv = w64 WVC_COMMA ->
     YK11.getr (ms_regs ms') 12%bv = w64 1 ->
     YK11.getr (ms_regs ms') 21%bv = w64 (i + 1) ->
     YK11.getr (ms_regs ms') 23%bv = w64 (56 * (i + 1)) ->
     YK11.getr (ms_regs ms') 25%bv = w64 (8 * (i + 1)) ->
     YK11.getr (ms_regs ms') 2%bv = YK11.getr (ms_regs ms) 2%bv ->
     (forall q, In q [3;4;8;9;18;19;20;22;24;26;27]%bv ->
        YK11.getr (ms_regs ms') q = YK11.getr (ms_regs ms) q) ->
     SRr tfibsegs W (mkCfg ms' mdc') Q) ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros W ms mdc E ty p i n keys STK sp0 spF FP ly S W0 mem md own lyc Sc U k Q
  (HS & SHOK & HJ & HARU) Hty H21 H23 H35 H36 H51 Hi0 Hin Hn Hk0 Hkn E2 Hsp HSTK HQ.
pose proof asan_consts as (HC1 & _).
assert (RSTART : forall q : bv 5,
  YK11.getr (ms_regs ms) q = sv_denot E (sr_get (ss_regs (wvc_ssL ty p WVC_R_ITEM)) q))
  by (intros q; exact (st_ok_restrict_reg tfibsegs (w_H W) E _ ms q HS)).
destruct Hty as [-> | ->].
all: destruct (Z.eq_dec p 0) as [->|Hp];
  [ idtac
  | rewrite (wvc_ssL_p1 _ p WVC_R_ITEM Hp) in HS, RSTART; rewrite (wvc_csL_p1 p Hp) in HQ ].
all: (lazymatch type of HS with st_ok _ _ ?ss0 _ =>
  assert (HSB : st_ok tfibsegs E
       (add_cond (add_cond ss0 (mkAC BC_LTU (SOff 21 1) (SOff (xatom 3) 0))) (mkAC BC_NE (SOff 21 1) (SLit 0)))
       (restrict (w_H W) ms)) end);
  [ apply (st_ok_add_cond tfibsegs E _ _ BC_NE (SOff 21 1) (SLit 0));
    [ apply (st_ok_add_cond tfibsegs E _ _ BC_LTU (SOff 21 1) (SOff (xatom 3) 0) HS);
      rewrite branch_ltu_U, (wvc_u_off E 21 i 1 H21 ltac:(lia) ltac:(lia)),
        (wvc_u_off E (xatom 3) n 0 H36 ltac:(lia) ltac:(lia));
      apply Z.ltb_lt; lia
    | rewrite branch_ne_U, (wvc_u_off E 21 i 1 H21 ltac:(lia) ltac:(lia)), U_SLit;
      unfold zcanon, M64; rewrite (Z.mod_small 0 (2 ^ 64)) by lia;
      apply negb_true_iff, Z.eqb_neq; lia ]
  | clear HS; rename HSB into HS ].
all: fsw_aj_run_to_tokU fsw_wr_tbl_ok HS HJ HARU SHOK fs_Bspan A_put;
  [ eapply wvc_awrL; [exact E2 | exact Hsp | exact HSTK]
  | apply HQ;
    [ wvc_shape
    | exact HJ
    | exact HARU
    | intros x Hx; cbn [add_cond ss_mem] in HFr; exact (wvc_outL _ _ _ _ _ _ _ HFr E2 x Hx)
    | eapply wvc_chunksL; [exact HS | vm_compute; reflexivity | exact E2]
    | eapply wvc_regL; [exact HS | vm_compute; reflexivity | unfold WVC_R_COMMA; lia]
    | eapply wvc_regE; [exact HS | vm_compute; reflexivity]
    | eapply wvc_regL; [exact HS | vm_compute; reflexivity | unfold WVC_COMMA; lia]
    | eapply wvc_regL; [exact HS | vm_compute; reflexivity | lia]
    | eapply (wvc_regU _ _ _ _ 21%bv (SOff 21 1));
      [ exact HS | vm_compute; reflexivity | exact (wvc_u_off E 21 i 1 H21 ltac:(lia) ltac:(lia)) ]
    | eapply (wvc_regU _ _ _ _ 23%bv (SOff 23 56));
      [ exact HS | vm_compute; reflexivity
      | rewrite (wvc_u_off E 23 (56 * i) 56 H23 ltac:(lia) ltac:(lia)); lia ]
    | eapply (wvc_regU _ _ _ _ 25%bv
        (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff (xatom 2) 0) (SLit (-1))) (SLit 8))
           (SOff (xatom 18) 0)));
      [ exact HS | vm_compute; reflexivity
      | rewrite (wvc_u_cursor E (xatom 2) (xatom 18) keys (keys + 8 * i) H35 H51
                   ltac:(lia) ltac:(lia) ltac:(lia)); lia ]
    | wvc_same E W
    | wvc_keep E W ] ].
Qed.

(* ================= (6) the last item's write_value returned: call the closing indent ================= *)
(* No UBSan guard is on this run (the loop test at 0x84298 takes the negated loop condition, `beqz n` at 0x842b0 the
   state's n <> 0). *)
Lemma wvc_seg_item_last : forall (W : world tfibsegs) ms mdc E ty p i n d keys
    STK sp0 spF FP ly S W0 mem md own lyc Sc U k (Q : world tfibsegs -> config -> Prop),
  wvc_at B E (wvc_ssL ty p WVC_R_ITEM) (wvc_SHL ty) W ms STK sp0 FP ly S W0 mem md own lyc Sc U mdc k ->
  ty = 5 \/ ty = 6 ->
  ew E 21 = Z_to_bv 64 i -> ew E 23 = Z_to_bv 64 (56 * i) ->
  ew E (xatom 2) = Z_to_bv 64 keys -> ew E (xatom 3) = Z_to_bv 64 n -> ew E (xatom 4) = Z_to_bv 64 d ->
  ew E (xatom 18) = Z_to_bv 64 (keys + 8 * i) ->
  0 <= i -> i + 1 = n -> n <= 2 ^ 54 -> 0 <= keys -> keys + 8 * n <= alloc_ceiling ->
  0 <= d -> d < 2 ^ 31 ->
  bv_unsigned (ew E 2) = spF - WVC_F -> spF <= sp0 -> sp0 - STK <= spF - WVC_F ->
  (forall ms' mdc',
     ms' = mkst (ms_regs ms') (w64 A_indent) (ms_mem ms') (seg_rom tfibsegs) ->
     ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U (ms_mem ms')) mdc' k ->
     ARU tfibsegs B lyc Sc U W (ms_mem ms') mdc' ->
     (forall x : word, ~ (spF - WVC_F <= bv_unsigned x < spF) ->
        mrestrict (w_H W) (ms_mem ms') x = mrestrict (w_H W) (ms_mem ms) x) ->
     Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W) (ms_mem ms')) (spF - WVC_F)) (wvc_csL p) ->
     YK11.getr (ms_regs ms') 1%bv = w64 WVC_R_CLOSE ->
     YK11.getr (ms_regs ms') 10%bv = ew E 8 ->
     YK11.getr (ms_regs ms') 11%bv = ew E 19 ->
     YK11.getr (ms_regs ms') 12%bv = w64 d ->
     YK11.getr (ms_regs ms') 21%bv = w64 (i + 1) ->
     YK11.getr (ms_regs ms') 23%bv = w64 (56 * (i + 1)) ->
     YK11.getr (ms_regs ms') 25%bv = w64 (8 * (i + 1)) ->
     YK11.getr (ms_regs ms') 2%bv = YK11.getr (ms_regs ms) 2%bv ->
     (forall q, In q [3;4;8;9;18;19;20;22;24;26;27]%bv ->
        YK11.getr (ms_regs ms') q = YK11.getr (ms_regs ms) q) ->
     SRr tfibsegs W (mkCfg ms' mdc') Q) ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros W ms mdc E ty p i n d keys STK sp0 spF FP ly S W0 mem md own lyc Sc U k Q
  (HS & SHOK & HJ & HARU) Hty H21 H23 H35 H36 H37 H51 Hi0 Hin Hn Hk0 Hkn Hd0 Hd1 E2 Hsp HSTK HQ.
pose proof asan_consts as (HC1 & _).
assert (RSTART : forall q : bv 5,
  YK11.getr (ms_regs ms) q = sv_denot E (sr_get (ss_regs (wvc_ssL ty p WVC_R_ITEM)) q))
  by (intros q; exact (st_ok_restrict_reg tfibsegs (w_H W) E _ ms q HS)).
destruct Hty as [-> | ->].
all: destruct (Z.eq_dec p 0) as [->|Hp];
  [ idtac
  | rewrite (wvc_ssL_p1 _ p WVC_R_ITEM Hp) in HS, RSTART; rewrite (wvc_csL_p1 p Hp) in HQ ].
all: (lazymatch type of HS with st_ok _ _ ?ss0 _ =>
  assert (HSB : st_ok tfibsegs E
       (add_cond ss0 (mkAC (neg_bc BC_LTU) (SOff 21 1) (SOff (xatom 3) 0))) (restrict (w_H W) ms)) end);
  [ apply (st_ok_add_cond_neg tfibsegs E _ _ BC_LTU (SOff 21 1) (SOff (xatom 3) 0) HS);
    rewrite branch_ltu_U, (wvc_u_off E 21 i 1 H21 ltac:(lia) ltac:(lia)),
      (wvc_u_off E (xatom 3) n 0 H36 ltac:(lia) ltac:(lia));
    apply Z.ltb_ge; lia
  | clear HS; rename HSB into HS ].
all: fsw_aj_run_to_tokU fsw_wr_tbl_ok HS HJ HARU SHOK fs_Bspan A_indent;
  [ eapply wvc_awrL; [exact E2 | exact Hsp | exact HSTK]
  | apply HQ;
    [ wvc_shape
    | exact HJ
    | exact HARU
    | intros x Hx; cbn [add_cond ss_mem] in HFr; exact (wvc_outL _ _ _ _ _ _ _ HFr E2 x Hx)
    | eapply wvc_chunksL; [exact HS | vm_compute; reflexivity | exact E2]
    | eapply wvc_regL; [exact HS | vm_compute; reflexivity | unfold WVC_R_CLOSE; lia]
    | eapply wvc_regE; [exact HS | vm_compute; reflexivity]
    | eapply wvc_regE; [exact HS | vm_compute; reflexivity]
    | eapply (wvc_regU _ _ _ _ 12%bv (SOff (xatom 4) 0));
      [ exact HS | vm_compute; reflexivity
      | rewrite (wvc_u_off E (xatom 4) d 0 H37 ltac:(lia) ltac:(lia)); lia ]
    | eapply (wvc_regU _ _ _ _ 21%bv (SOff 21 1));
      [ exact HS | vm_compute; reflexivity | exact (wvc_u_off E 21 i 1 H21 ltac:(lia) ltac:(lia)) ]
    | eapply (wvc_regU _ _ _ _ 23%bv (SOff 23 56));
      [ exact HS | vm_compute; reflexivity
      | rewrite (wvc_u_off E 23 (56 * i) 56 H23 ltac:(lia) ltac:(lia)); lia ]
    | eapply (wvc_regU _ _ _ _ 25%bv
        (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff (xatom 2) 0) (SLit (-1))) (SLit 8))
           (SOff (xatom 18) 0)));
      [ exact HS | vm_compute; reflexivity
      | rewrite (wvc_u_cursor E (xatom 2) (xatom 18) keys (keys + 8 * i) H35 H51
                   ltac:(lia) ltac:(lia) ltac:(lia)); lia ]
    | wvc_same E W
    | wvc_keep E W ] ].
Qed.

(* ================= (7) the comma's put returned: call the next item's indent ================= *)
(* UBSan guard 0x8418c (`bnez s10`, the signed overflow of d + 1): the engine decides it, s10 is SLit 0 in wvc_ssL
   (wvc_Lregs; the open run took it under wvc_cSLT). *)
Lemma wvc_seg_comma : forall (W : world tfibsegs) ms mdc E ty p d
    STK sp0 spF FP ly S W0 mem md own lyc Sc U k (Q : world tfibsegs -> config -> Prop),
  wvc_at B E (wvc_ssL ty p WVC_R_COMMA) (wvc_SHL ty) W ms STK sp0 FP ly S W0 mem md own lyc Sc U mdc k ->
  ty = 5 \/ ty = 6 ->
  ew E (xatom 4) = Z_to_bv 64 d -> 0 <= d -> d + 1 < 2 ^ 31 ->
  bv_unsigned (ew E 2) = spF - WVC_F -> spF <= sp0 -> sp0 - STK <= spF - WVC_F ->
  (forall ms' mdc',
     ms' = mkst (ms_regs ms') (w64 A_indent) (ms_mem ms') (seg_rom tfibsegs) ->
     ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U (ms_mem ms')) mdc' k ->
     ARU tfibsegs B lyc Sc U W (ms_mem ms') mdc' ->
     (forall x : word, ~ (spF - WVC_F <= bv_unsigned x < spF) ->
        mrestrict (w_H W) (ms_mem ms') x = mrestrict (w_H W) (ms_mem ms) x) ->
     Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W) (ms_mem ms')) (spF - WVC_F)) (wvc_csL p) ->
     YK11.getr (ms_regs ms') 1%bv = w64 WVC_R_IND ->
     YK11.getr (ms_regs ms') 10%bv = ew E 8 ->
     YK11.getr (ms_regs ms') 11%bv = ew E 19 ->
     YK11.getr (ms_regs ms') 12%bv = w64 (d + 1) ->
     YK11.getr (ms_regs ms') 2%bv = YK11.getr (ms_regs ms) 2%bv ->
     (forall q, In q [3;4;8;9;18;19;20;21;22;23;24;25;26;27]%bv ->
        YK11.getr (ms_regs ms') q = YK11.getr (ms_regs ms) q) ->
     SRr tfibsegs W (mkCfg ms' mdc') Q) ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros W ms mdc E ty p d STK sp0 spF FP ly S W0 mem md own lyc Sc U k Q
  (HS & SHOK & HJ & HARU) Hty H37 Hd0 Hd1 E2 Hsp HSTK HQ.
assert (RSTART : forall q : bv 5,
  YK11.getr (ms_regs ms) q = sv_denot E (sr_get (ss_regs (wvc_ssL ty p WVC_R_COMMA)) q))
  by (intros q; exact (st_ok_restrict_reg tfibsegs (w_H W) E _ ms q HS)).
destruct Hty as [-> | ->].
all: destruct (Z.eq_dec p 0) as [->|Hp];
  [ idtac
  | rewrite (wvc_ssL_p1 _ p WVC_R_COMMA Hp) in HS, RSTART; rewrite (wvc_csL_p1 p Hp) in HQ ].
all: fsw_aj_run_to_tokU fsw_wr_tbl_ok HS HJ HARU SHOK fs_Bspan A_indent;
  [ eapply wvc_awrL; [exact E2 | exact Hsp | exact HSTK]
  | apply HQ;
    [ wvc_shape
    | exact HJ
    | exact HARU
    | intros x Hx; exact (wvc_outL _ _ _ _ _ _ _ HFr E2 x Hx)
    | eapply wvc_chunksL; [exact HS | vm_compute; reflexivity | exact E2]
    | eapply wvc_regL; [exact HS | vm_compute; reflexivity | unfold WVC_R_IND; lia]
    | eapply wvc_regE; [exact HS | vm_compute; reflexivity]
    | eapply wvc_regE; [exact HS | vm_compute; reflexivity]
    | eapply (wvc_regU _ _ _ _ 12%bv (SAlu ALU_ADD (SAluw ALU_ADD (SOff (xatom 4) 0) (SLit 1)) (SLit 0)));
      [ exact HS | vm_compute; reflexivity | exact (wvc_u_d1 E (xatom 4) d H37 Hd0 Hd1) ]
    | wvc_same E W
    | wvc_keep E W ] ].
Qed.

(* ================= (8) the closing indent returned: TAIL-jump to put of the closing bracket ================= *)
(* No UBSan guard is on this run. *)
Lemma wvc_seg_close : forall (W : world tfibsegs) ms mdc E ty p
    STK sp0 spF FP ly S W0 mem md own lyc Sc U k (Q : world tfibsegs -> config -> Prop),
  wvc_at B E (wvc_ssL ty p WVC_R_CLOSE) (wvc_SHL ty) W ms STK sp0 FP ly S W0 mem md own lyc Sc U mdc k ->
  ty = 5 \/ ty = 6 ->
  bv_unsigned (ew E 2) = spF - WVC_F -> spF <= sp0 -> sp0 - STK <= spF - WVC_F -> spF < 2 ^ 64 ->
  (forall ms' mdc',
     ms' = mkst (ms_regs ms') (w64 A_put) (ms_mem ms') (seg_rom tfibsegs) ->
     ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U (ms_mem ms')) mdc' k ->
     ARU tfibsegs B lyc Sc U W (ms_mem ms') mdc' ->
     (forall x : word, ~ (spF - WVC_F <= bv_unsigned x < spF) ->
        mrestrict (w_H W) (ms_mem ms') x = mrestrict (w_H W) (ms_mem ms) x) ->
     YK11.getr (ms_regs ms') 1%bv = ew E (xatom 17) ->
     YK11.getr (ms_regs ms') 10%bv = ew E 8 ->
     YK11.getr (ms_regs ms') 11%bv = w64 (wvc_close ty) ->
     YK11.getr (ms_regs ms') 12%bv = w64 1 ->
     YK11.getr (ms_regs ms') 2%bv = Z_to_bv 64 spF ->
     YK11.getr (ms_regs ms') 3%bv = ew E 3 ->
     YK11.getr (ms_regs ms') 4%bv = ew E 4 ->
     (forall j : nat, (j < 13)%nat ->
        YK11.getr (ms_regs ms') (nth j wvc_saved 0%bv) = ew E (xatom (5 + j))) ->
     SRr tfibsegs W (mkCfg ms' mdc') Q) ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros W ms mdc E ty p STK sp0 spF FP ly S W0 mem md own lyc Sc U k Q
  (HS & SHOK & HJ & HARU) Hty E2 Hsp HSTK Hsp64 HQ.
assert (RSTART : forall q : bv 5,
  YK11.getr (ms_regs ms) q = sv_denot E (sr_get (ss_regs (wvc_ssL ty p WVC_R_CLOSE)) q))
  by (intros q; exact (st_ok_restrict_reg tfibsegs (w_H W) E _ ms q HS)).
destruct Hty as [-> | ->].
all: destruct (Z.eq_dec p 0) as [->|Hp];
  [ idtac | rewrite (wvc_ssL_p1 _ p WVC_R_CLOSE Hp) in HS, RSTART ].
all: fsw_aj_run_to_tokU fsw_wr_tbl_ok HS HJ HARU SHOK fs_Bspan A_put;
  [ eapply wvc_awrL; [exact E2 | exact Hsp | exact HSTK]
  | apply HQ;
    [ wvc_shape
    | exact HJ
    | exact HARU
    | intros x Hx; exact (wvc_outL _ _ _ _ _ _ _ HFr E2 x Hx)
    | eapply wvc_regE; [exact HS | vm_compute; reflexivity]
    | eapply wvc_regE; [exact HS | vm_compute; reflexivity]
    | eapply wvc_regL; [exact HS | vm_compute; reflexivity | apply wvc_close_range]
    | eapply wvc_regL; [exact HS | vm_compute; reflexivity | lia]
    | eapply (wvc_regU _ _ _ _ 2%bv (SOff 2 WVC_F));
      [ exact HS | vm_compute; reflexivity
      | pose proof (u64_range (ew E 2)) as HR2; rewrite E2 in HR2; rewrite U_SOff, E2;
        unfold zcanon, M64, WVC_F in *; rewrite Z.mod_small by lia; lia ]
    | eapply wvc_regE; [exact HS | vm_compute; reflexivity]
    | eapply wvc_regE; [exact HS | vm_compute; reflexivity]
    | intros j Hj;
      do 13 (destruct j as [|j];
        [ cbn [nth wvc_saved Nat.add]; eapply wvc_regE; [exact HS | vm_compute; reflexivity] | ]);
      exfalso; lia ] ].
Qed.

(* ================= (8') the closing indent returned, from the close-point state wvc_ssN (node alone):
   TAIL-jump to put of the closing bracket ================= *)
(* No UBSan guard is on this run. *)
Lemma wvc_seg_closeN : forall (W : world tfibsegs) ms mdc E ty p
    STK sp0 spF FP ly S W0 mem md own lyc Sc U k (Q : world tfibsegs -> config -> Prop),
  wvc_at B E (wvc_ssN ty p) wvc_SH0 W ms STK sp0 FP ly S W0 mem md own lyc Sc U mdc k ->
  ty = 5 \/ ty = 6 ->
  bv_unsigned (ew E 2) = spF - WVC_F -> spF <= sp0 -> sp0 - STK <= spF - WVC_F -> spF < 2 ^ 64 ->
  (forall ms' mdc',
     ms' = mkst (ms_regs ms') (w64 A_put) (ms_mem ms') (seg_rom tfibsegs) ->
     ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U (ms_mem ms')) mdc' k ->
     ARU tfibsegs B lyc Sc U W (ms_mem ms') mdc' ->
     (forall x : word, ~ (spF - WVC_F <= bv_unsigned x < spF) ->
        mrestrict (w_H W) (ms_mem ms') x = mrestrict (w_H W) (ms_mem ms) x) ->
     YK11.getr (ms_regs ms') 1%bv = ew E (xatom 17) ->
     YK11.getr (ms_regs ms') 10%bv = ew E 8 ->
     YK11.getr (ms_regs ms') 11%bv = w64 (wvc_close ty) ->
     YK11.getr (ms_regs ms') 12%bv = w64 1 ->
     YK11.getr (ms_regs ms') 2%bv = Z_to_bv 64 spF ->
     YK11.getr (ms_regs ms') 3%bv = ew E 3 ->
     YK11.getr (ms_regs ms') 4%bv = ew E 4 ->
     (forall j : nat, (j < 13)%nat ->
        YK11.getr (ms_regs ms') (nth j wvc_saved 0%bv) = ew E (xatom (5 + j))) ->
     SRr tfibsegs W (mkCfg ms' mdc') Q) ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros W ms mdc E ty p STK sp0 spF FP ly S W0 mem md own lyc Sc U k Q
  (HS & SHOK & HJ & HARU) Hty E2 Hsp HSTK Hsp64 HQ.
assert (RSTART : forall q : bv 5,
  YK11.getr (ms_regs ms) q = sv_denot E (sr_get (ss_regs (wvc_ssN ty p)) q))
  by (intros q; exact (st_ok_restrict_reg tfibsegs (w_H W) E _ ms q HS)).
destruct Hty as [-> | ->].
all: destruct (Z.eq_dec p 0) as [->|Hp];
  [ idtac | rewrite (wvc_ssN_p1 _ p Hp) in HS, RSTART ].
all: fsw_aj_run_to_tokU fsw_wr_tbl_ok HS HJ HARU SHOK fs_Bspan A_put;
  [ eapply wvc_awrN; [exact E2 | exact Hsp | exact HSTK]
  | apply HQ;
    [ wvc_shape
    | exact HJ
    | exact HARU
    | intros x Hx; exact (wvc_outN _ _ _ _ _ _ HFr E2 x Hx)
    | eapply wvc_regE; [exact HS | vm_compute; reflexivity]
    | eapply wvc_regE; [exact HS | vm_compute; reflexivity]
    | eapply wvc_regL; [exact HS | vm_compute; reflexivity | apply wvc_close_range]
    | eapply wvc_regL; [exact HS | vm_compute; reflexivity | lia]
    | eapply (wvc_regU _ _ _ _ 2%bv (SOff 2 WVC_F));
      [ exact HS | vm_compute; reflexivity
      | pose proof (u64_range (ew E 2)) as HR2; rewrite E2 in HR2; rewrite U_SOff, E2;
        unfold zcanon, M64, WVC_F in *; rewrite Z.mod_small by lia; lia ]
    | eapply wvc_regE; [exact HS | vm_compute; reflexivity]
    | eapply wvc_regE; [exact HS | vm_compute; reflexivity]
    | intros j Hj;
      do 13 (destruct j as [|j];
        [ cbn [nth wvc_saved Nat.add]; eapply wvc_regE; [exact HS | vm_compute; reflexivity] | ]);
      exfalso; lia ] ].
Qed.

End W.
