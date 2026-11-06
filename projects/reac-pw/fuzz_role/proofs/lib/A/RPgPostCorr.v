(* reac-pw/fuzz_role image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; addresses measured on the unstripped twin
   6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6): one turn of the corruption loop of
   LLVMFuzzerTestOneInput (0x7ff88), pod.h:445-446 with fuzz.h:39-42. Proves no function (kind: segment lemma).
   THE CODE (the cut R = 0x82018 is the loop head; a3 = kk, a2 = cnt - kk, a4 = off, a0 the cursor, a5 what is left
   of the input)
     0x82018 lbu a1,0(s4) / bnez a1 -> 0x82b48           the shadow byte of &pp->len (s4 = (pp + 0x4000 >> 3) + K)
     0x82020 ld a6,0(s5) / add a1,a4,a3                  len, off + kk
     0x82028 bgeu a1,a6 -> 0x82094                       off + kk >= len: the corruption ends (RT)
     0x8202c beqz a5 -> 0x82050                          no input left: the byte is 0 (0x82050 mv a6,zero)
     0x82030 .. 0x8203c                                  the check of the 1-byte read at a0 (slow test 0x82088)
     0x82040 lbu a6,0(a0) / addi a0,a0,1 / addi a5,a5,-1 / j 0x82054
     0x82054 add a1,s11,a1                               pp + off + kk
     0x82058 .. 0x82064                                  the check of the 1-byte store at a1 (slow test 0x8207c)
     0x82068 sb a6,0(a1) / addi a2,a2,-1 / addi a3,a3,1
     0x82074 bnez a2 -> 0x82018                          the next turn (R with kk + 1)
     0x82078 j 0x82094                                   the count is done (RT)
   The engine meets the two computed addresses through the facts' aliases: off + kk is atom 33 and
   pp + off + kk atom 34, so the store lands in a region of its own; each access's shadow bytes are a shadow
   entry of the engine (the length word and the store target inside the first block, the input byte inside the
   input), so no check reaches its error path.
   w10_corr: the statement rs_piece_W10_corr_stmt (lib/A/RPgSeg.v), R kk -> R (kk + 1) or RT. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgBase RPgCSpec RPgImgA RPgMem RPgSeg RPgSiteA.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require RPgCfgChanges.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgW7bBase RPgW6cKit RPgPostK.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Local Arguments x_STK {segs} _. Local Arguments x_sp0 {segs} _. Local Arguments x_FP {segs} _.
Local Arguments x_ly {segs} _. Local Arguments x_S {segs} _. Local Arguments x_W0 {segs} _.
Local Arguments x_mem0 {segs} _. Local Arguments x_md0 {segs} _. Local Arguments x_own {segs} _.
Local Arguments x_k {segs} _. Local Arguments x_regs {segs} _. Local Arguments x_lyc {segs} _.
Local Arguments x_Sc {segs} _. Local Arguments x_W {segs} _. Local Arguments x_memc {segs} _.
Local Arguments x_mdc {segs} _. Local Arguments x_RLO {segs} _. Local Arguments x_RHI {segs} _.
Local Arguments x_e {segs} _. Local Arguments x_pos {segs} _.

(* ---- the input byte at the cursor ---- *)
Lemma w10c_nth_skipn : forall (rest : list byte) j x r1, skipn j rest = x :: r1 -> nth j (rs_u8s rest) 0 = bv_unsigned x.
Proof.
unfold rs_u8s. induction rest as [|y rest IH]; intros [|j] x r1 H; cbn in H |- *; try discriminate.
- injection H as -> ->. reflexivity.
- exact (IH j x r1 H).
Qed.

(* the sum of two atoms, as the engine writes `add` *)
Lemma w10c_den_add : forall E n1 n2 v1 v2, ew E n1 = Z_to_bv 64 v1 -> 0 <= v1 < 2 ^ 62 ->
  ew E n2 = Z_to_bv 64 v2 -> 0 <= v2 < 2 ^ 62 ->
  sv_denot E (SAlu ALU_ADD (SOff n1 0) (SOff n2 0)) = Z_to_bv 64 (v1 + v2).
Proof.
intros E n1 n2 v1 v2 H1 B1 H2 B2. rewrite denot_lit_U. f_equal.
rewrite U_SAlu, (U_atom E n1 v1 H1 ltac:(lia)), (U_atom E n2 v2 H2 ltac:(lia)). cbn [zalu_raw].
apply zcanon_id. unfold M64. lia.
Qed.

(* the shadow entry of one input byte *)
Lemma w10c_shent_in : forall E m n src left c, amem_range src left -> U E W10Bx = SHADOW_OFF ->
  U E (SOff n 0) = c -> src <= c -> c + 1 <= src + left ->
  range_addressable (rd_of rsegs m) SHADOW_OFF src left ->
  shent_ok rsegs W10Bx E m (mkSHE n 0 1).
Proof.
intros E m n src left c Ham HB Hc H1 H2 Hra. split; cbn [she_m she_lo she_hi].
- rewrite HB, Hc. eapply range_addressable_sub; [exact Hra | lia | lia].
- unfold app_apart. cbn [she_m she_lo she_hi]. intros a Ha. rewrite HB. rewrite Hc in Ha.
  change (Z.min 0 1) with 0 in Ha. change (Z.max 0 1) with 1 in Ha.
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *. lia.
Qed.

(* a nonempty suffix: its head is the next byte of the prefix *)
Lemma w10c_skipn_cons : forall (l : list byte) k y l', skipn k l = y :: l' ->
  firstn (S k) l = firstn k l ++ [y] /\ skipn (S k) l = l'.
Proof.
induction l as [|z l IH]; intros [|k] y l' H; cbn in H |- *; try discriminate.
- injection H as -> ->. split; reflexivity.
- destruct (IH k y l' H) as [H1 H2]. split; [rewrite H1; reflexivity | exact H2].
Qed.

Lemma w10c_le1 : forall y : byte, Z_to_le_bytes 1 (bv_unsigned y) = [y].
Proof. intros y. cbn [Z_to_le_bytes]. rewrite w10_byte_self. reflexivity. Qed.

(* the block after the store of the corruption's byte kk *)
Lemma w10c_img_next : forall (cx : rs_scx rsegs) W2 mem2 mem3 sh ps off bs kk (y : byte),
  rs_wf sh ps -> 8 <= off -> (kk < length bs)%nat -> off + Z.of_nat (length bs) <= rs_plen sh ps ->
  rs_pp_at rsegs cx W2 mem2 (rs_img_corr sh ps off bs (Z.of_nat kk)) ->
  val_mem rsegs (mrestrict (w_H W2) mem3) (e_pp (x_e cx) + off + Z.of_nat kk) 1 (bv_unsigned y) ->
  (forall a, e_pp (x_e cx) <= a < e_pp (x_e cx) + PP_SIZE -> a <> e_pp (x_e cx) + off + Z.of_nat kk ->
     aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  firstn (S kk) bs = firstn kk bs ++ [y] ->
  rs_pp_at rsegs cx W2 mem3 (rs_img_corr sh ps off bs (Z.of_nat (S kk))).
Proof.
intros cx W2 mem2 mem3 sh ps off bs kk y Hwf Hoff Hk Hob Hpp Hv HK Hfs.
destruct (w10_wf_facts sh ps Hwf) as (HW1 & HW2 & HW3 & HW4 & _).
unfold rs_plen in Hob.
unfold rs_pp_at, rs_img_corr in *. rewrite Nat2Z.id in *. rewrite Hfs.
assert (Hl : length (firstn kk bs) = kk) by (rewrite length_firstn; lia).
rewrite <- (w10_img_step sh ps off (firstn kk bs) y ltac:(lia) ltac:(rewrite Hl; lia)).
rewrite Hl. rewrite <- (w10c_le1 y).
set (IMG := pp_image (overwrite (pod_encode (PodRec sh ps None)) (Z.to_nat off) (firstn kk bs))
  (is_props (PodRec sh ps None)) (has_params (PodRec sh ps None)) (params_struct (PodRec sh ps None))
  (ents (PodRec sh ps None)) false) in *.
assert (HLl : Z.of_nat (length IMG) = PP_SIZE).
{ apply length_pp_image; [| exact HW3 | exact HW4].
  rewrite length_overwrite; [rewrite HW2; unfold POD_BUF_MAX; lia | rewrite Hl; lia]. }
unfold PP_SIZE in HLl.
apply (rm_bytes_store rsegs (w_H W2) mem2 (w_H W2) mem3 (e_pp (x_e cx)) _ (Z.to_nat off + kk) 1 (bv_unsigned y) Hpp).
- replace (e_pp (x_e cx) + Z.of_nat (Z.to_nat off + kk)) with (e_pp (x_e cx) + off + Z.of_nat kk) by lia. exact Hv.
- lia.
- intros z Hz Hn. apply HK; [unfold PP_SIZE; lia | lia].
Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

(* What one turn of the loop leaves, read off the turn's end: the journal clauses, the post cuts' values, the
   frame's shadow and the block with one more corruption byte. *)
Lemma w10c_turn_common : forall (cx : rs_scx rsegs) rest kk ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3
    sh ps off bs cnt r r' (y : byte),
  rs_pre rsegs B cx ->
  rs_cut_R rsegs B MT cx sh ps rest r off bs cnt (Z.of_nat kk) ly2 S2 W2 regs2 mem2 md2 ->
  ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    ly2 S2 W2 mem3 md3 (x_k cx) ->
  same_io md2 md3 ->
  (forall n : Z, In n [2; 3; 4; 8; 9; 19; 23; 21; 27; 25; 20; 26] ->
     getr regs3 (Z_to_bv 5 n) = getr regs2 (Z_to_bv 5 n)) ->
  (forall a, 0 <= a < 2 ^ 64 -> a <> e_pp (x_e cx) + off + Z.of_nat kk ->
     aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  val_mem rsegs (mrestrict (w_H W2) mem3) (e_pp (x_e cx) + off + Z.of_nat kk) 1 (bv_unsigned y) ->
  skipn kk bs = y :: fst (fuzz_u8s (length bs - S kk) r') ->
  rs_core rsegs B MT cx (rs_E1 rsegs cx) ly2 S2 W2 regs3 mem3 md3 /\
  rs_at_cx rsegs cx W2 mem3 regs3 (rs_L_post rsegs cx) /\
  rs_fsh_at rsegs cx W2 mem3 rs_P0 /\
  rs_pp_at rsegs cx W2 mem3 (rs_img_corr sh ps off bs (Z.of_nat (S kk))) /\
  (kk < length bs)%nat /\ skipn (S kk) bs = fst (fuzz_u8s (length bs - S kk) r').
Proof.
intros cx rest kk ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 sh ps off bs cnt r r' y HP HR HJ3 Hio3 Hregs HK Hv Hsk.
destruct HR as (HC & HL & Hfsh & Hpp & Hin & Hsuf & Hwf & Hlen & Htie & Hcw & Hkk & Hkb & Hskip).
destruct (w10_ctx B MT cx ly2 S2 W2 regs2 mem2 md2 HP HC)
  as (Hinp & Hfresh & Hal & Hlo & Hhi & Happ & Hpres & H2 & HR16 & HRS & HSTK & Hceil & H47 & HAR).
destruct (w10_F_ctx B cx HP) as (HF1 & HF2 & HF3).
destruct (w10_wf_facts sh ps Hwf) as (HW1 & HW2 & HW3 & HW4 & _).
pose proof Hcw as (Hoff & Hob & Hb7 & Hcnt & Hbmin). unfold rs_plen in Hob, Hbmin.
destruct (rs_pre_geom rsegs B cx HP) as (_ & X1 & X2 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hkl : (kk < length bs)%nat).
{ destruct (Nat.lt_ge_cases kk (length bs)) as [H|H]; [exact H|]. rewrite skipn_all2 in Hsk by exact H. discriminate. }
destruct (w10c_skipn_cons bs kk y _ Hsk) as [Hfs Hss].
assert (Hnp : forall a, e_R (x_e cx) - T_SEG_STK <= a -> a <> e_pp (x_e cx) + off + Z.of_nat kk).
{ intros a Ha. unfold T_SEG_STK, ASTACK in *. lia. }
assert (Hcell : forall o i, 0 <= o < 0x138 -> 0 <= i < 8 ->
  aview rsegs (w_H W2) mem3 (e_R (x_e cx) + o + i) = aview rsegs (w_H W2) mem2 (e_R (x_e cx) + o + i)).
{ intros o i Ho Hi. apply HK; [unfold kHighMemBeg, T_SEG_STK, ASTACK in *; lia | apply Hnp; unfold T_SEG_STK, ASTACK; lia]. }
split; [|split; [|split; [|split; [|split; [exact Hkl | exact Hss]]]]].
- apply (w10_core_run B MT cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 (fun a => a = e_pp (x_e cx) + off + Z.of_nat kk) HC HJ3).
  + intros rr Hr. apply Hregs. destruct Hr as [->|[->| ->]]; cbn; tauto.
  + exact Hio3.
  + intros a Ha Hn. exact (HK a Ha Hn).
  + intros a ->. right. unfold PP_SIZE. lia.
- pose proof HL as HLp. unfold rs_at_cx, rs_at in HLp. apply Forall_app in HLp. destruct HLp as [HLp _].
  apply (rm_atl_kept rsegs (w_H W2) mem2 (w_H W2) mem3 regs2 regs3 (x_e cx) _ HLp).
  intros f Hf. unfold rs_L_post in Hf. cbv zeta in Hf.
  repeat (destruct Hf as [<-|Hf]; [cbn [fst rm_keeps rl_xv];
    first [ (apply Hregs; cbn; tauto) | (intros i Hi; apply Hcell; lia) ] |]).
  destruct Hf.
- apply (rm_fsh_kept rsegs (w_H W2) mem2 (w_H W2) mem3 (e_F (x_e cx)) rs_P0 Hfsh).
  intros i Hi. change (length rs_P0) with 52%nat in Hi.
  pose proof (Z.div_pos (e_F (x_e cx)) 8 ltac:(lia)). assert (e_F (x_e cx) / 8 < 2 ^ 47) by (apply Z.div_lt_upper_bound; lia).
  pose proof (w10_shadow_not_pp (e_pp (x_e cx)) (e_F (x_e cx)) i Happ HF3 ltac:(lia)) as Hs.
  apply HK; [unfold shadow_addr, SHADOW_OFF; lia | unfold PP_SIZE in Hs; lia].
- apply (w10c_img_next cx W2 mem2 mem3 sh ps off bs kk y Hwf Hoff Hkl Hob Hpp Hv); [| exact Hfs].
  intros a Ha Hn. apply HK; [unfold PP_SIZE in Ha; lia | exact Hn].
Qed.

Lemma w10c_finish_R : forall (cx : rs_scx rsegs) rest kk ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3
    sh ps off bs cnt r r' (y : byte),
  rs_pre rsegs B cx ->
  rs_cut_R rsegs B MT cx sh ps rest r off bs cnt (Z.of_nat kk) ly2 S2 W2 regs2 mem2 md2 ->
  ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    ly2 S2 W2 mem3 md3 (x_k cx) ->
  same_io md2 md3 ->
  (forall n : Z, In n [2; 3; 4; 8; 9; 19; 23; 21; 27; 25; 20; 26] ->
     getr regs3 (Z_to_bv 5 n) = getr regs2 (Z_to_bv 5 n)) ->
  (forall a, 0 <= a < 2 ^ 64 -> a <> e_pp (x_e cx) + off + Z.of_nat kk ->
     aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  val_mem rsegs (mrestrict (w_H W2) mem3) (e_pp (x_e cx) + off + Z.of_nat kk) 1 (bv_unsigned y) ->
  skipn kk bs = y :: fst (fuzz_u8s (length bs - S kk) r') ->
  rs_suffix rest r' ->
  getr regs3 (Z_to_bv 5 13) = w64 (Z.of_nat (S kk)) ->
  getr regs3 (Z_to_bv 5 12) = w64 (cnt - Z.of_nat (S kk)) ->
  getr regs3 (Z_to_bv 5 14) = w64 off ->
  getr regs3 (Z_to_bv 5 10) = w64 (rs_cur rsegs cx rest r') ->
  getr regs3 (Z_to_bv 5 15) = w64 (Z.of_nat (length r')) ->
  Z.of_nat (S kk) < cnt ->
  rs_cut_R rsegs B MT cx sh ps rest r' off bs cnt (Z.of_nat (S kk)) ly2 S2 W2 regs3 mem3 md3.
Proof.
intros cx rest kk ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 sh ps off bs cnt r r' y HP HR HJ3 Hio3 Hregs HK Hv Hsk Hsuf'
  R13 R12 R14 R10 R15 Hlt.
destruct (w10c_turn_common cx rest kk ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 sh ps off bs cnt r r' y
  HP HR HJ3 Hio3 Hregs HK Hv Hsk) as (Hcore & HLp & Hfsh & Hpp & Hkl & Hss).
destruct HR as (_ & _ & _ & _ & Hin & _ & Hwf & Hlen & Htie & Hcw & _ & _ & _).
split; [exact Hcore|]. split.
{ unfold rs_at_cx, rs_at in *. apply Forall_app. split; [exact HLp|].
  repeat (apply Forall_cons; [cbn [fst snd rl_at]; assumption |]). apply Forall_nil. }
split; [exact Hfsh|]. split; [exact Hpp|]. split; [exact Hin|]. split; [exact Hsuf'|]. split; [exact Hwf|].
split; [exact Hlen|]. split; [exact Htie|]. split; [exact Hcw|]. split; [lia|]. split; [lia|].
rewrite Nat2Z.id. exact Hss.
Qed.

Lemma w10c_finish_RT : forall (cx : rs_scx rsegs) rest kk ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3
    sh ps off bs cnt r r' (y : byte),
  rs_pre rsegs B cx ->
  rs_cut_R rsegs B MT cx sh ps rest r off bs cnt (Z.of_nat kk) ly2 S2 W2 regs2 mem2 md2 ->
  ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    ly2 S2 W2 mem3 md3 (x_k cx) ->
  same_io md2 md3 ->
  (forall n : Z, In n [2; 3; 4; 8; 9; 19; 23; 21; 27; 25; 20; 26] ->
     getr regs3 (Z_to_bv 5 n) = getr regs2 (Z_to_bv 5 n)) ->
  (forall a, 0 <= a < 2 ^ 64 -> a <> e_pp (x_e cx) + off + Z.of_nat kk ->
     aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  val_mem rsegs (mrestrict (w_H W2) mem3) (e_pp (x_e cx) + off + Z.of_nat kk) 1 (bv_unsigned y) ->
  skipn kk bs = y :: fst (fuzz_u8s (length bs - S kk) r') ->
  rs_suffix rest r' ->
  length bs = S kk ->
  rs_cut_RT rsegs B MT cx sh ps off bs rest r' ly2 S2 W2 regs3 mem3 md3.
Proof.
intros cx rest kk ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 sh ps off bs cnt r r' y HP HR HJ3 Hio3 Hregs HK Hv Hsk Hsuf'
  Hbl.
destruct (w10c_turn_common cx rest kk ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 sh ps off bs cnt r r' y
  HP HR HJ3 Hio3 Hregs HK Hv Hsk) as (Hcore & HLp & Hfsh & Hpp & Hkl & Hss).
destruct HR as (_ & _ & _ & _ & Hin & _ & Hwf & Hlen & Htie & Hcw & _ & _ & _).
destruct Hcw as (Hoff & Hob & Hb7 & _).
split; [exact Hcore|]. split; [exact HLp|]. split; [exact Hfsh|]. split; [rewrite Hbl; exact Hpp|].
split; [exact Hin|]. split; [exact Hsuf'|]. split; [exact Hwf|]. split; [exact Hlen|]. split; [exact Htie|].
split; [exact Hoff|]. split; [exact Hob | exact Hb7].
Qed.

Theorem w10_corr : rs_piece_W10_corr_stmt rsegs B MT.
Proof.
unfold rs_piece_W10_corr_stmt. intros cx POST rest kk Hst HR1 HRT.
unfold rs_from_R. intros ly2 S2 W2 regs2 mem2 md2 sh ps r off bs cnt HR.
destruct Hst as (HP & _ & _ & _).
pose proof HR as HRc.
destruct HR as (HC & HL & Hfsh & Hpp & Hin & Hsuf & Hwf & Hlen & Htie & Hcw & Hkk & Hkb & Hskip).
pose proof RPgCfgChanges.cfg_wx as Hwx. pose proof RPgCfgChanges.cfg_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
destruct (w10_ctx B MT cx ly2 S2 W2 regs2 mem2 md2 HP HC)
  as (Hinp & Hfresh & Hal & Hlo & Hhi & Happ & Hpres & H2 & HR16 & HRS & HSTK & Hceil & H47 & HAR).
destruct (w10_F_ctx B cx HP) as (HF1 & HF2 & HF3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (w10_wf_facts sh ps Hwf) as (HW1 & HW2 & HW3 & HW4 & HW5).
destruct Hcw as (Hoff & Hob & Hb7 & Hcnt & Hbmin).
unfold rs_plen in Hob, Hbmin.
destruct (rs_in_now rsegs B MT cx rest rs_P0 ly2 S2 W2 regs2 mem2 md2 HP Hin HC Hfsh eq_refl) as (Hbytes & Hra & _).
pose proof Hin as (Hleft & _ & _ & _ & Hamr & Hsrc0 & Hsrc63 & Hindisj).
destruct Hsuf as (j & Hj & Hrj).
set (pp := e_pp (x_e cx)) in *.
set (Lp := Z.of_nat (length (pc_buf (PbCut sh ps None)))) in *.
set (enc := pod_encode (PodRec sh ps None)) in *.
rewrite Nat2Z.id in Hskip.
assert (Hbl : length (overwrite enc (Z.to_nat off) (firstn kk bs)) = length (pc_buf (PbCut sh ps None))).
{ rewrite length_overwrite; [exact HW2|]. rewrite length_firstn. lia. }
assert (HLv : val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 0x4000) 8 Lp).
{ unfold rs_pp_at, rs_img_corr in Hpp. rewrite Nat2Z.id in Hpp.
  pose proof (rm_pp_len rsegs (overwrite enc (Z.to_nat off) (firstn kk bs)) _ _ _ _ _
    ltac:(rewrite Hbl; unfold POD_BUF_MAX; lia) HW3 HW4 (w_H W2) mem2 pp Hpp) as X.
  rewrite Hbl in X. exact X. }
pose proof HL as HL0.
unfold rs_at_cx, rs_at, rs_L_post in HL. cbv zeta in HL. cbn [app] in HL.
rewrite !Forall_cons_iff in HL.
destruct HL as (P8 & P9 & P19 & P23 & P21 & P27 & P25 & P20 & P26 & Q8 & Q28 & Q30 & Q68 & Q78 & Q80 &
  P13 & P12 & P14 & P10 & P15 & _).
cbn [fst snd rl_at] in P8, P9, P19, P23, P21, P27, P25, P20, P26, P13, P12, P14, P10, P15.
pose proof HC as (HJ & _).
change (e_pp (x_e cx)) with pp in P21, P27, P20, P26.
set (cur := rs_cur rsegs cx rest r) in P10.
assert (Hcur : cur = e_src (x_e cx) + Z.of_nat j).
{ subst cur. unfold rs_cur. rewrite Hrj, length_skipn. lia. }
assert (Hrl : Z.of_nat (length r) = Z.of_nat (length rest) - Z.of_nat j) by (rewrite Hrj, length_skipn; lia).
assert (HK47 : e_src (x_e cx) + e_left (x_e cx) <= 2 ^ 47 - 1)
  by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; lia).
set (src := e_src (x_e cx)) in Hcur, HK47, Hamr, Hsrc0, Hsrc63, Hra, Hbytes, Hindisj.
set (kz := Z.of_nat kk) in P13, P12, Hkk, Hkb, Hpp.
remember (Ereg regs2 [Z_to_bv 64 Lp; Z_to_bv 64 (off + kz); Z_to_bv 64 (pp + off + kz);
  Z_to_bv 64 (match r with x :: _ => bv_unsigned x | [] => 0 end)]) as E eqn:HE.
assert (E10 : ew E 10 = Z_to_bv 64 cur) by (subst E; rewrite (ew_Ereg_nat regs2 _ 10 (Z_to_bv 5 10) eq_refl); exact P10).
assert (E12 : ew E 12 = Z_to_bv 64 (cnt - kz)) by (subst E; rewrite (ew_Ereg_nat regs2 _ 12 (Z_to_bv 5 12) eq_refl); exact P12).
assert (E13 : ew E 13 = Z_to_bv 64 kz) by (subst E; rewrite (ew_Ereg_nat regs2 _ 13 (Z_to_bv 5 13) eq_refl); exact P13).
assert (E14 : ew E 14 = Z_to_bv 64 off) by (subst E; rewrite (ew_Ereg_nat regs2 _ 14 (Z_to_bv 5 14) eq_refl); exact P14).
assert (E15 : ew E 15 = Z_to_bv 64 (Z.of_nat (length r))) by (subst E; rewrite (ew_Ereg_nat regs2 _ 15 (Z_to_bv 5 15) eq_refl); exact P15).
assert (E21 : ew E 21 = Z_to_bv 64 (pp + 0x4000)) by (subst E; rewrite (ew_Ereg_nat regs2 _ 21 (Z_to_bv 5 21) eq_refl); exact P21).
assert (E23 : ew E 23 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite (ew_Ereg_nat regs2 _ 23 (Z_to_bv 5 23) eq_refl); exact P23).
assert (E27 : ew E 27 = Z_to_bv 64 pp) by (subst E; rewrite (ew_Ereg_nat regs2 _ 27 (Z_to_bv 5 27) eq_refl); exact P27).
assert (E32 : ew E 32 = Z_to_bv 64 Lp) by (subst E; exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (off + kz)) by (subst E; exact (ew_Ereg_extra regs2 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (pp + off + kz)) by (subst E; exact (ew_Ereg_extra regs2 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (match r with x :: _ => bv_unsigned x | [] => 0 end))
  by (subst E; exact (ew_Ereg_extra regs2 _ 3)).
assert (HB : U E W10Bx = SHADOW_OFF) by exact (w10_U_atom E 23 SHADOW_OFF E23 ltac:(unfold SHADOW_OFF; lia)).
assert (Hpp47 : 0 <= pp + 0x4000 < 2 ^ 47) by lia.
assert (HoffL : off + kz <= Lp) by lia.
pose proof HL0 as HLpost. unfold rs_at_cx, rs_at in HLpost. apply Forall_app in HLpost. destruct HLpost as [HLpost _].
assert (HAE : env_agree 32 (Ereg regs2 [Z_to_bv 64 Lp; Z_to_bv 64 (off + kz); Z_to_bv 64 (pp + off + kz);
  Z_to_bv 64 (match r with x :: _ => bv_unsigned x | [] => 0 end)]) E)
  by (rewrite HE; split; [intros; reflexivity | reflexivity]).
assert (HRk : 0 <= e_R (x_e cx) - T_SEG_STK /\ e_R (x_e cx) + 0x1a0 <= 2 ^ 47).
{ destruct (rs_pre_geom rsegs B cx HP) as (_ & X1 & X2 & _). unfold kHighMemBeg in X1. lia. }
assert (Himgl : forall k, (k <= length bs)%nat -> Z.of_nat (length (rs_img_corr sh ps off bs (Z.of_nat k))) = PP_SIZE).
{ intros k Hk. unfold rs_img_corr. fold enc. apply length_pp_image; [| exact HW3 | exact HW4].
  rewrite length_overwrite; [rewrite HW2; unfold POD_BUF_MAX; lia|]. rewrite length_firstn. lia. }
destruct (Z_le_gt_dec Lp (off + kz)) as [Hge|Hlt].
{ (* off + kk reaches the length: the corruption ends with the bytes written so far *)
  assert (Hkbs : kz = Z.of_nat (length bs)) by lia.
  assert (HS : st_ok rsegs E (mkSS 0x82018
    (sr_set sr_atoms (Z_to_bv 5 20) (SAlu ALU_ADD (SAlu ALU_SRL (SOff 21 0) (SLit 3)) (SOff 23 0)))
    [YP09.mkRegion (Some 21%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))]] None
    (mkFacts [(21%nat, mkAF 4096 W10_HI 4); (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 8 5440 0);
              (33%nat, mkAF 8 5447 0); (12%nat, mkAF 1 7 0); (13%nat, mkAF 0 6 0); (14%nat, mkAF 8 5440 0)]
       [mkAC BC_GEU (SOff 33 0) (SOff 32 0)]
       [(SAlu ALU_ADD (SOff 13 0) (SOff 14 0), SOff 33 0)]))
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 0x82018) mem2 (seg_rom rsegs)))).
  { rewrite restrict_mkst_fx. subst E. apply (entry_st_ok_full rsegs).
    - apply regs_ok_pin; [apply regs_ok_Ereg | intros X; apply (f_equal (@bv_unsigned 5)) in X; vm_compute in X; discriminate X |].
      rewrite (w10_den_sh _ 21 23 (pp + 0x4000) E21 ltac:(lia) E23). exact P20.
    - vm_compute. reflexivity.
    - constructor; [|constructor].
      apply (rm_ro_region rsegs _ (w_H W2) mem2 21 (pp + 0x4000)).
      + rewrite E21. rewrite unsigned_lit_small by lia. reflexivity.
      + lia. + lia.
      + constructor; [|constructor]. apply (chunk_ok_val rsegs _ _ (pp + 0x4000) 0 8 (SOff 32 0) Lp).
        * exact (w10_den_atom _ 32 Lp E32). * cbn. lia. * cbn. lia. * rewrite Z.add_0_r. exact HLv.
    - cbn. tauto.
    - unfold facts_ok. cbn [f_atoms f_conds f_alias conds_ok alias_ok].
      refine (conj _ (conj (conj _ I) (conj _ I))).
      + cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite E21, E23, E32, E33, E12, E13, E14.
        rewrite !unsigned_lit_small by (unfold SHADOW_OFF, W10_HI; lia).
        repeat match goal with |- _ /\ _ => split end; try exact I; try (unfold SHADOW_OFF, W10_HI; lia);
        try (rewrite Z.pow_0_r; apply Z.mod_1_r).
        change (2 ^ 4) with 16. rewrite Z.add_mod by lia. rewrite Hal. reflexivity.
      + unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_geu_U, (w10_U_atom _ 33 _ E33 ltac:(lia)), (w10_U_atom _ 32 _ E32 ltac:(lia)).
        apply negb_true_iff, Z.ltb_ge. lia.
      + rewrite (w10c_den_add _ 13 14 kz off E13 ltac:(lia) E14 ltac:(lia)), (w10_den_atom _ 33 _ E33). f_equal. lia. }
  assert (SHOK : sh_ok rsegs W10Bx [mkSHE 21 0 8] E (mrestrict (w_H W2) mem2)).
  { constructor; [|constructor].
    apply (w10_shent_blk B ly2 S2 W2 mem2 md2 E pp PP_SIZE 21 0 8 HAR Hinp);
    change (req_size PP_SIZE) with 19744; [exact Happ | exact HB | | | lia];
    rewrite (w10_U_atom E 21 _ E21 ltac:(lia)); lia. }
  unfold cfg_at. change (w64 RS_R) with (Z_to_bv 64 0x82018).
  aj_run_to_tok w10_tbl_ok HS HJ SHOK W10Bspan 0x82094.
  { cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  assert (HK : forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W2) (ms_mem ms) a = aview rsegs (w_H W2) mem2 a).
  { intros a Ha. apply (w10_frame_kept _ _ _ _ _ HFr a Ha). intros (rg & Hr & Hrb). cbn [ss_mem] in Hr.
    destruct Hr as [<-|[]]. cbn in Hrb. lia. }
  pose proof (w7_regs_kept _ _ ms regs2 _ (w_H W2) [Z_to_bv 5 11; Z_to_bv 5 16; Z_to_bv 5 20] HS HAE
    ltac:(vm_compute; reflexivity)) as RK.
  assert (RK20 : getr (ms_regs ms) (Z_to_bv 5 20) = getr regs2 (Z_to_bv 5 20)).
  { rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms (Z_to_bv 5 20) HS). w10_sr_eval.
    rewrite (w10_den_sh _ 21 23 (pp + 0x4000) E21 ltac:(lia) E23). symmetry. exact P20. }
  assert (Hcell : forall o i, 0 <= o < 0x138 -> 0 <= i < 8 ->
    aview rsegs (w_H W2) (ms_mem ms) (e_R (x_e cx) + o + i) = aview rsegs (w_H W2) mem2 (e_R (x_e cx) + o + i)).
  { intros o i Ho Hi. apply HK. unfold T_SEG_STK, ASTACK in *. lia. }
  rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
  apply (HRT ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ sh ps off bs r).
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]]].
  - apply (w10_core_run B MT cx ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ (fun _ => False) HC HJ).
    + intros rr Hr. apply RK; [destruct Hr as [->|[->| ->]]; vm_compute; discriminate |].
      apply w10_notin. destruct Hr as [->|[->| ->]]; vm_compute; reflexivity.
    + apply RPgCfgChanges.same_io_wvb.
    + intros a Ha _. exact (HK a Ha).
    + intros a [].
  - apply (rm_atl_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) regs2 (ms_regs ms) (x_e cx) _ HLpost).
    intros f Hf. unfold rs_L_post in Hf. cbv zeta in Hf.
    repeat (destruct Hf as [<-|Hf]; [cbn [fst rm_keeps rl_xv];
      first [ exact RK20
            | (apply RK; [vm_compute; discriminate | apply w10_notin; vm_compute; reflexivity])
            | (intros i Hi; apply Hcell; lia) ] |]).
    destruct Hf.
  - apply (rm_fsh_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) (e_F (x_e cx)) rs_P0 Hfsh).
    intros i Hi. apply HK. change (length rs_P0) with 52%nat in Hi.
    pose proof (Z.div_pos (e_F (x_e cx)) 8 ltac:(lia)). assert (e_F (x_e cx) / 8 < 2 ^ 47) by (apply Z.div_lt_upper_bound; lia).
    unfold shadow_addr, SHADOW_OFF. lia.
  - rewrite <- Hkbs. apply (rm_bytes_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) pp _ Hpp).
    assert (X : Z.of_nat (length (rs_img_corr sh ps off bs kz)) = PP_SIZE) by exact (Himgl kk ltac:(lia)).
    intros y Hy. rewrite X in Hy. apply HK. unfold PP_SIZE in Hy. lia.
  - exact Hin.
  - exists j. split; [exact Hj | exact Hrj].
  - exact Hwf.
  - exact Hlen.
  - exact Htie.
  - exact Hoff.
  - unfold rs_plen. exact Hob.
  - exact Hb7. }
destruct r as [|x r1].
{ (* no input left: the byte is 0 *)
  cbv beta iota in E35, HE, HAE.
  assert (Hkl : (kk < length bs)%nat) by (unfold kz in *; lia).
  assert (Hsk : skipn kk bs = Z_to_bv 8 0 :: fst (fuzz_u8s (length bs - S kk) [])).
  { rewrite Hskip. replace (length bs - kk)%nat with (S (length bs - S kk)) by lia. apply w10_fuzz_u8s_nil. }
  assert (Hsuf' : rs_suffix rest []) by (exists j; split; [exact Hj | exact Hrj]).
  assert (Hy0 : bv_unsigned (Z_to_bv 8 0 : byte) = 0) by reflexivity.
  change (Z.of_nat (length (@nil byte))) with 0 in E15.
assert (HS : st_ok rsegs E (mkSS 0x82018
  (sr_set sr_atoms (Z_to_bv 5 20) (SAlu ALU_ADD (SAlu ALU_SRL (SOff 21 0) (SLit 3)) (SOff 23 0)))
  [YP09.mkRegion (Some 34%nat) 0 1 0 1 [];
   YP09.mkRegion (Some 21%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))]] None
  (mkFacts [(21%nat, mkAF 4096 W10_HI 4); (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 8 5440 0);
            (33%nat, mkAF 8 5440 0); (34%nat, mkAF 4096 W10_HI 0);
            (15%nat, mkAF 0 0 0); (12%nat, mkAF 1 7 0);
            (13%nat, mkAF 0 6 0); (14%nat, mkAF 8 5440 0)]
     [mkAC BC_LTU (SOff 33 0) (SOff 32 0); mkAC BC_EQ (SOff 15 0) (SLit 0)]
     [(SAlu ALU_ADD (SOff 13 0) (SOff 14 0), SOff 33 0); (SAlu ALU_ADD (SOff 27 0) (SOff 33 0), SOff 34 0)]))
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 0x82018) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. subst E. apply (entry_st_ok_full rsegs).
  - apply regs_ok_pin; [apply regs_ok_Ereg | intros X; apply (f_equal (@bv_unsigned 5)) in X; vm_compute in X; discriminate X |].
    rewrite (w10_den_sh _ 21 23 (pp + 0x4000) E21 ltac:(lia) E23). exact P20.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + apply (rm_rw_region rsegs _ (w_H W2) mem2 34 (pp + off + kz)).
      * rewrite E34. rewrite unsigned_lit_small by lia. reflexivity.
      * lia. * lia.
      * intros o Ho. apply Hpres. lia.
      * constructor.
    + apply (rm_ro_region rsegs _ (w_H W2) mem2 21 (pp + 0x4000)).
      * rewrite E21. rewrite unsigned_lit_small by lia. reflexivity.
      * lia. * lia.
      * constructor; [|constructor]. apply (chunk_ok_val rsegs _ _ (pp + 0x4000) 0 8 (SOff 32 0) Lp).
        -- exact (w10_den_atom _ 32 Lp E32). -- cbn. lia. -- cbn. lia. -- rewrite Z.add_0_r. exact HLv.
  - apply pairwise_disjoint_of_extents.
    cbn [map zpairwise_disjoint zall_disjoint]. unfold YA0q.extent_of_region, zdisj.
    cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi fst snd].
    rewrite E34, E21, !unsigned_lit_small by lia.
    repeat split; lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias conds_ok alias_ok].
    refine (conj _ (conj (conj _ (conj _ I)) (conj _ (conj _ I)))).
    + cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E21, E23, E32, E33, E34, E15, E12, E13, E14.
      rewrite !unsigned_lit_small by (unfold SHADOW_OFF, W10_HI; lia).
      repeat match goal with |- _ /\ _ => split end; try exact I; try (unfold SHADOW_OFF, W10_HI; lia);
      try (rewrite Z.pow_0_r; apply Z.mod_1_r).
      change (2 ^ 4) with 16. rewrite Z.add_mod by lia. rewrite Hal. reflexivity.
    + unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_ltu_U, (w10_U_atom _ 33 _ E33 ltac:(lia)), (w10_U_atom _ 32 _ E32 ltac:(lia)).
      apply Z.ltb_lt. lia.
    + unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_eq_U, (w10_U_atom _ 15 0 E15 ltac:(lia)), U_lit by lia.
      reflexivity.
    + rewrite (w10c_den_add _ 13 14 kz off E13 ltac:(lia) E14 ltac:(lia)), (w10_den_atom _ 33 _ E33). f_equal. lia.
    + rewrite (w10c_den_add _ 27 33 pp (off + kz) E27 ltac:(lia) E33 ltac:(lia)), (w10_den_atom _ 34 _ E34). f_equal. lia. }
(* the shadow entries: the store target and the length word inside the first block, the input byte *)
assert (SHOK : sh_ok rsegs W10Bx [mkSHE 34 0 1; mkSHE 21 0 8] E (mrestrict (w_H W2) mem2)).
{ constructor; [|constructor; [|constructor]].
  - apply (w10_shent_blk B ly2 S2 W2 mem2 md2 E pp PP_SIZE 34 0 1 HAR Hinp);
    change (req_size PP_SIZE) with 19744; [exact Happ | exact HB | | | lia];
    rewrite (w10_U_atom E 34 _ E34 ltac:(lia)); lia.
  - apply (w10_shent_blk B ly2 S2 W2 mem2 md2 E pp PP_SIZE 21 0 8 HAR Hinp);
    change (req_size PP_SIZE) with 19744; [exact Happ | exact HB | | | lia];
    rewrite (w10_U_atom E 21 _ E21 ltac:(lia)); lia. }
unfold cfg_at. change (w64 RS_R) with (Z_to_bv 64 0x82018).
aj_run_to_tok w10_tbl_ok HS HJ SHOK W10Bspan 0x82094.
{ cbn [ss_mem].
  eapply (w10_awr_cons_pp E _ _ _ _ _ _ _ _ _ 34%nat (pp + off + kz) pp);
    [reflexivity | | exact Hinp | exact Hfresh | cbn; lia | cbn; unfold PP_SIZE; lia |].
  { rewrite E34. apply unsigned_lit_small. lia. }
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename ms into msA. rename HF into HFa. rename HFr into HFra. rename HG into HGa.
srr_branch_tok w10_tbl_ok HS SHOK W10Bspan.
- (* a2 - 1 <> 0: the next turn *)
  aj_run_to_tok w10_tbl_ok HS HJ SHOK W10Bspan 0x82018.
  { cbn [ss_mem add_cond].
    eapply (w10_awr_cons_pp _ _ _ _ _ _ _ _ _ _ 34%nat (pp + off + kz) pp);
      [reflexivity | | exact Hinp | exact Hfresh | cbn; lia | cbn; unfold PP_SIZE; lia |].
    { rewrite ?ew_ewset_other by lia. rewrite E34. apply unsigned_lit_small. lia. }
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  rewrite branch_ne_U in Hc. rewrite (U_atom_off _ 12 (cnt - kz) (-1)) in Hc;
    [| rewrite !ew_ewset_other by lia; exact E12 | lia | lia].
  rewrite U_lit in Hc by lia.
  apply negb_true_iff, Z.eqb_neq in Hc.

  assert (HKAB : forall a, 0 <= a < 2 ^ 64 -> a <> pp + off + kz ->
    aview rsegs (w_H W2) (ms_mem ms) a = aview rsegs (w_H W2) mem2 a).
  { intros a Ha Hn. transitivity (aview rsegs (w_H W2) (ms_mem msA) a).
    - apply (w10_frame_kept _ _ _ _ _ HFr a Ha). intros (rg & Hr & Hrb). cbn [ss_mem add_cond] in Hr.
      destruct Hr as [<-|[<-|[]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb; [|lia].
      rewrite !ew_ewset_other in Hrb by lia. rewrite E34, unsigned_lit_small in Hrb by lia. apply Hn. lia.
    - apply (w10_frame_kept _ _ _ _ _ HFra a Ha). intros (rg & Hr & Hrb). cbn [ss_mem] in Hr.
      destruct Hr as [<-|[<-|[]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb; [|lia].
      rewrite E34, unsigned_lit_small in Hrb by lia. apply Hn. lia. }
  assert (Hv : val_mem rsegs (mrestrict (w_H W2) (ms_mem ms)) (pp + off + kz) 1 (bv_unsigned (Z_to_bv 8 0 : byte))).
  { rewrite Hy0. pose proof (w7_region_nth _ _ _ 0 _ HS eq_refl) as HR0.
    replace (pp + off + kz) with (pp + off + kz + 0) by lia.
    apply (w7_field _ _ 34 (pp + off + kz) _ 0 1 0 1 0 1 (SLit 0) 0 HR0);
      [ rewrite !ew_ewset_other by lia; rewrite E34; apply unsigned_lit_small; lia
      | left; reflexivity
      | reflexivity
      | cbn; lia | cbn; lia ]. }
  pose proof (w7_regs_kept _ _ ms regs2 _ (w_H W2)
    [Z_to_bv 5 5; Z_to_bv 5 11; Z_to_bv 5 12; Z_to_bv 5 13; Z_to_bv 5 16; Z_to_bv 5 17; Z_to_bv 5 20] HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as RK.
  assert (RK20 : getr (ms_regs ms) (Z_to_bv 5 20) = getr regs2 (Z_to_bv 5 20)).
  { rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms (Z_to_bv 5 20) HS). w10_sr_eval.
    rewrite (w10_den_sh _ 21 23 (pp + 0x4000));
      [symmetry; exact P20 | rewrite !ew_ewset_other by lia; exact E21 | exact Hpp47
      | rewrite !ew_ewset_other by lia; exact E23]. }
  assert (Hregs : forall n : Z, In n [2; 3; 4; 8; 9; 19; 23; 21; 27; 25; 20; 26] ->
    getr (ms_regs ms) (Z_to_bv 5 n) = getr regs2 (Z_to_bv 5 n)).
  { intros n Hn. cbn [In] in Hn.
    repeat (destruct Hn as [<-|Hn];
      [first [exact RK20 | (apply RK; [vm_compute; discriminate | apply w10_notin; vm_compute; reflexivity])] |]).
    destruct Hn. }
  assert (R13 : getr (ms_regs ms) (Z_to_bv 5 13) = w64 (Z.of_nat (S kk))).
  { rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms (Z_to_bv 5 13) HS). w10_sr_eval.
    rewrite (w10_den_off _ 13 kz 1) by (rewrite !ew_ewset_other by lia; exact E13).
    f_equal. unfold kz. lia. }
  assert (R12 : getr (ms_regs ms) (Z_to_bv 5 12) = w64 (cnt - Z.of_nat (S kk))).
  { rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms (Z_to_bv 5 12) HS). w10_sr_eval.
    rewrite (w10_den_off _ 12 (cnt - kz) (-1)) by (rewrite !ew_ewset_other by lia; exact E12).
    f_equal. unfold kz. lia. }
  assert (R14 : getr (ms_regs ms) (Z_to_bv 5 14) = w64 off).
  { rewrite RK; [exact P14 | vm_compute; discriminate | apply w10_notin; vm_compute; reflexivity]. }
  assert (R10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (rs_cur rsegs cx rest [])).
  { rewrite RK; [exact P10 | vm_compute; discriminate | apply w10_notin; vm_compute; reflexivity]. }
  assert (R15 : getr (ms_regs ms) (Z_to_bv 5 15) = w64 (Z.of_nat (length (@nil byte)))).
  { rewrite RK; [exact P15 | vm_compute; discriminate | apply w10_notin; vm_compute; reflexivity]. }
  rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
  apply (HR1 ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ sh ps [] off bs cnt).
  apply (w10c_finish_R cx rest kk ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ sh ps off bs cnt [] [] (Z_to_bv 8 0)
    HP HRc HJ ltac:(eapply same_io_trans; apply RPgCfgChanges.same_io_wvb) Hregs HKAB Hv Hsk Hsuf' R13 R12 R14 R10 R15).
  unfold kz in *. lia.
- (* a2 - 1 = 0: the count is done *)
  aj_run_to_tok w10_tbl_ok HS HJ SHOK W10Bspan 0x82094.
  { cbn [ss_mem add_cond].
    eapply (w10_awr_cons_pp _ _ _ _ _ _ _ _ _ _ 34%nat (pp + off + kz) pp);
      [reflexivity | | exact Hinp | exact Hfresh | cbn; lia | cbn; unfold PP_SIZE; lia |].
    { rewrite ?ew_ewset_other by lia. rewrite E34. apply unsigned_lit_small. lia. }
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  rewrite branch_ne_U in Hc. rewrite (U_atom_off _ 12 (cnt - kz) (-1)) in Hc;
    [| rewrite !ew_ewset_other by lia; exact E12 | lia | lia].
  rewrite U_lit in Hc by lia.
  apply negb_false_iff, Z.eqb_eq in Hc.

  assert (HKAB : forall a, 0 <= a < 2 ^ 64 -> a <> pp + off + kz ->
    aview rsegs (w_H W2) (ms_mem ms) a = aview rsegs (w_H W2) mem2 a).
  { intros a Ha Hn. transitivity (aview rsegs (w_H W2) (ms_mem msA) a).
    - apply (w10_frame_kept _ _ _ _ _ HFr a Ha). intros (rg & Hr & Hrb). cbn [ss_mem add_cond] in Hr.
      destruct Hr as [<-|[<-|[]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb; [|lia].
      rewrite !ew_ewset_other in Hrb by lia. rewrite E34, unsigned_lit_small in Hrb by lia. apply Hn. lia.
    - apply (w10_frame_kept _ _ _ _ _ HFra a Ha). intros (rg & Hr & Hrb). cbn [ss_mem] in Hr.
      destruct Hr as [<-|[<-|[]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb; [|lia].
      rewrite E34, unsigned_lit_small in Hrb by lia. apply Hn. lia. }
  assert (Hv : val_mem rsegs (mrestrict (w_H W2) (ms_mem ms)) (pp + off + kz) 1 (bv_unsigned (Z_to_bv 8 0 : byte))).
  { rewrite Hy0. pose proof (w7_region_nth _ _ _ 0 _ HS eq_refl) as HR0.
    replace (pp + off + kz) with (pp + off + kz + 0) by lia.
    apply (w7_field _ _ 34 (pp + off + kz) _ 0 1 0 1 0 1 (SLit 0) 0 HR0);
      [ rewrite !ew_ewset_other by lia; rewrite E34; apply unsigned_lit_small; lia
      | left; reflexivity
      | reflexivity
      | cbn; lia | cbn; lia ]. }
  pose proof (w7_regs_kept _ _ ms regs2 _ (w_H W2)
    [Z_to_bv 5 5; Z_to_bv 5 11; Z_to_bv 5 12; Z_to_bv 5 13; Z_to_bv 5 16; Z_to_bv 5 17; Z_to_bv 5 20] HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as RK.
  assert (RK20 : getr (ms_regs ms) (Z_to_bv 5 20) = getr regs2 (Z_to_bv 5 20)).
  { rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms (Z_to_bv 5 20) HS). w10_sr_eval.
    rewrite (w10_den_sh _ 21 23 (pp + 0x4000));
      [symmetry; exact P20 | rewrite !ew_ewset_other by lia; exact E21 | exact Hpp47
      | rewrite !ew_ewset_other by lia; exact E23]. }
  assert (Hregs : forall n : Z, In n [2; 3; 4; 8; 9; 19; 23; 21; 27; 25; 20; 26] ->
    getr (ms_regs ms) (Z_to_bv 5 n) = getr regs2 (Z_to_bv 5 n)).
  { intros n Hn. cbn [In] in Hn.
    repeat (destruct Hn as [<-|Hn];
      [first [exact RK20 | (apply RK; [vm_compute; discriminate | apply w10_notin; vm_compute; reflexivity])] |]).
    destruct Hn. }
  assert (Hbs : length bs = S kk) by (unfold kz in *; lia).
  rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
  apply (HRT ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ sh ps off bs []).
  exact (w10c_finish_RT cx rest kk ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ sh ps off bs cnt [] [] (Z_to_bv 8 0)
    HP HRc HJ ltac:(eapply same_io_trans; apply RPgCfgChanges.same_io_wvb) Hregs HKAB Hv Hsk Hsuf' Hbs).
}
cbv beta iota in E35, HE, HAE.
assert (Hjr : (j < length rest)%nat) by (cbn [length] in Hrl; lia).
assert (Hkl : (kk < length bs)%nat) by (unfold kz in *; lia).
assert (Hsk : skipn kk bs = x :: fst (fuzz_u8s (length bs - S kk) r1)).
{ rewrite Hskip. replace (length bs - kk)%nat with (S (length bs - S kk)) by lia. apply w10_fuzz_u8s_cons. }
assert (Hsuf' : rs_suffix rest r1).
{ exists (S j). split; [lia | symmetry; exact (proj2 (w10c_skipn_cons rest j x r1 (eq_sym Hrj)))]. }
assert (Hx : val_mem rsegs (mrestrict (w_H W2) mem2) cur 1 (bv_unsigned x)).
{ destruct (garr8_nthZ rsegs _ _ _ (Z.of_nat j) Hbytes ltac:(lia) ltac:(unfold rs_u8s; rewrite length_map; lia)) as [V _].
  rewrite Nat2Z.id, (w10c_nth_skipn rest j x r1 (eq_sym Hrj)) in V. rewrite Hcur. exact V. }
pose proof (bv_unsigned_in_range _ x) as Hxr. unfold bv_modulus in Hxr. change (Z.of_N 8) with 8 in Hxr.
assert (HS : st_ok rsegs E (mkSS 0x82018
  (sr_set sr_atoms (Z_to_bv 5 20) (SAlu ALU_ADD (SAlu ALU_SRL (SOff 21 0) (SLit 3)) (SOff 23 0)))
  [YP09.mkRegion (Some 34%nat) 0 1 0 1 [];
   YP09.mkRegion (Some 21%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))];
   YP09.mkRegion (Some 10%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 35 0))]] None
  (mkFacts [(21%nat, mkAF 4096 W10_HI 4); (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 8 5440 0);
            (33%nat, mkAF 8 5440 0); (34%nat, mkAF 4096 W10_HI 0); (35%nat, mkAF 0 255 0);
            (10%nat, mkAF 1 (2 ^ 47 - 2) 0); (15%nat, mkAF 1 (2 ^ 47) 0); (12%nat, mkAF 1 7 0);
            (13%nat, mkAF 0 6 0); (14%nat, mkAF 8 5440 0)] [mkAC BC_LTU (SOff 33 0) (SOff 32 0)]
     [(SAlu ALU_ADD (SOff 13 0) (SOff 14 0), SOff 33 0); (SAlu ALU_ADD (SOff 27 0) (SOff 33 0), SOff 34 0)]))
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 0x82018) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. subst E. apply (entry_st_ok_full rsegs).
  - apply regs_ok_pin; [apply regs_ok_Ereg | intros X; apply (f_equal (@bv_unsigned 5)) in X; vm_compute in X; discriminate X |].
    rewrite (w10_den_sh _ 21 23 (pp + 0x4000) E21 ltac:(lia) E23). exact P20.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor; [|constructor]]].
    + apply (rm_rw_region rsegs _ (w_H W2) mem2 34 (pp + off + kz)).
      * rewrite E34. rewrite unsigned_lit_small by lia. reflexivity.
      * lia. * lia.
      * intros o Ho. apply Hpres. lia.
      * constructor.
    + apply (rm_ro_region rsegs _ (w_H W2) mem2 21 (pp + 0x4000)).
      * rewrite E21. rewrite unsigned_lit_small by lia. reflexivity.
      * lia. * lia.
      * constructor; [|constructor]. apply (chunk_ok_val rsegs _ _ (pp + 0x4000) 0 8 (SOff 32 0) Lp).
        -- exact (w10_den_atom _ 32 Lp E32). -- cbn. lia. -- cbn. lia. -- rewrite Z.add_0_r. exact HLv.
    + apply (rm_ro_region rsegs _ (w_H W2) mem2 10 cur).
      * rewrite E10. rewrite unsigned_lit_small by lia. reflexivity.
      * lia. * lia.
      * constructor; [|constructor]. apply (chunk_ok_val rsegs _ _ cur 0 1 (SOff 35 0) (bv_unsigned x)).
        -- exact (w10_den_atom _ 35 _ E35). -- cbn. lia. -- cbn. lia. -- rewrite Z.add_0_r. exact Hx.
  - apply pairwise_disjoint_of_extents.
    cbn [map zpairwise_disjoint zall_disjoint]. unfold YA0q.extent_of_region, zdisj.
    cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi fst snd].
    rewrite E34, E21, E10, !unsigned_lit_small by lia.
    destruct (Hindisj cur ltac:(lia)) as (_ & _ & Hnp). unfold PP_SIZE in Hnp.
    repeat split; lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias conds_ok alias_ok].
    refine (conj _ (conj (conj _ I) (conj _ (conj _ I)))).
    + cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E21, E23, E32, E33, E34, E35, E10, E15, E12, E13, E14.
      rewrite !unsigned_lit_small by (unfold SHADOW_OFF, W10_HI; lia).
      repeat match goal with |- _ /\ _ => split end; try exact I; try (unfold SHADOW_OFF, W10_HI; lia);
      try (rewrite Z.pow_0_r; apply Z.mod_1_r).
      change (2 ^ 4) with 16. rewrite Z.add_mod by lia. rewrite Hal. reflexivity.
    + unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_ltu_U, (w10_U_atom _ 33 _ E33 ltac:(lia)), (w10_U_atom _ 32 _ E32 ltac:(lia)).
      apply Z.ltb_lt. lia.
    + rewrite (w10c_den_add _ 13 14 kz off E13 ltac:(lia) E14 ltac:(lia)), (w10_den_atom _ 33 _ E33). f_equal. lia.
    + rewrite (w10c_den_add _ 27 33 pp (off + kz) E27 ltac:(lia) E33 ltac:(lia)), (w10_den_atom _ 34 _ E34). f_equal. lia. }
(* the shadow entries: the store target and the length word inside the first block, the input byte *)
assert (SHOK : sh_ok rsegs W10Bx [mkSHE 34 0 1; mkSHE 21 0 8; mkSHE 10 0 1] E (mrestrict (w_H W2) mem2)).
{ constructor; [|constructor; [|constructor; [|constructor]]].
  - apply (w10_shent_blk B ly2 S2 W2 mem2 md2 E pp PP_SIZE 34 0 1 HAR Hinp);
    change (req_size PP_SIZE) with 19744; [exact Happ | exact HB | | | lia];
    rewrite (w10_U_atom E 34 _ E34 ltac:(lia)); lia.
  - apply (w10_shent_blk B ly2 S2 W2 mem2 md2 E pp PP_SIZE 21 0 8 HAR Hinp);
    change (req_size PP_SIZE) with 19744; [exact Happ | exact HB | | | lia];
    rewrite (w10_U_atom E 21 _ E21 ltac:(lia)); lia.
  - apply (w10c_shent_in E _ 10 src (e_left (x_e cx)) cur Hamr HB (w10_U_atom E 10 _ E10 ltac:(lia))); [lia | lia | exact Hra]. }
unfold cfg_at. change (w64 RS_R) with (Z_to_bv 64 0x82018).
aj_run_to_tok w10_tbl_ok HS HJ SHOK W10Bspan 0x82094.
{ cbn [ss_mem].
  eapply (w10_awr_cons_pp E _ _ _ _ _ _ _ _ _ 34%nat (pp + off + kz) pp);
    [reflexivity | | exact Hinp | exact Hfresh | cbn; lia | cbn; unfold PP_SIZE; lia |].
  { rewrite E34. apply unsigned_lit_small. lia. }
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename ms into msA. rename HF into HFa. rename HFr into HFra. rename HG into HGa.
srr_branch_tok w10_tbl_ok HS SHOK W10Bspan.
- (* a2 - 1 <> 0: the next turn *)
  aj_run_to_tok w10_tbl_ok HS HJ SHOK W10Bspan 0x82018.
  { cbn [ss_mem add_cond].
    eapply (w10_awr_cons_pp _ _ _ _ _ _ _ _ _ _ 34%nat (pp + off + kz) pp);
      [reflexivity | | exact Hinp | exact Hfresh | cbn; lia | cbn; unfold PP_SIZE; lia |].
    { rewrite ?ew_ewset_other by lia. rewrite E34. apply unsigned_lit_small. lia. }
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  rewrite branch_ne_U in Hc. rewrite (U_atom_off _ 12 (cnt - kz) (-1)) in Hc;
    [| rewrite !ew_ewset_other by lia; exact E12 | lia | lia].
  rewrite U_lit in Hc by lia.
  apply negb_true_iff, Z.eqb_neq in Hc.

  assert (HKAB : forall a, 0 <= a < 2 ^ 64 -> a <> pp + off + kz ->
    aview rsegs (w_H W2) (ms_mem ms) a = aview rsegs (w_H W2) mem2 a).
  { intros a Ha Hn. transitivity (aview rsegs (w_H W2) (ms_mem msA) a).
    - apply (w10_frame_kept _ _ _ _ _ HFr a Ha). intros (rg & Hr & Hrb). cbn [ss_mem add_cond] in Hr.
      destruct Hr as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb; [|lia|lia].
      rewrite !ew_ewset_other in Hrb by lia. rewrite E34, unsigned_lit_small in Hrb by lia. apply Hn. lia.
    - apply (w10_frame_kept _ _ _ _ _ HFra a Ha). intros (rg & Hr & Hrb). cbn [ss_mem] in Hr.
      destruct Hr as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb; [|lia|lia].
      rewrite E34, unsigned_lit_small in Hrb by lia. apply Hn. lia. }
  assert (Hv : val_mem rsegs (mrestrict (w_H W2) (ms_mem ms)) (pp + off + kz) 1 (bv_unsigned x)).
  { pose proof (w7_region_nth _ _ _ 0 _ HS eq_refl) as HR0.
    replace (pp + off + kz) with (pp + off + kz + 0) by lia.
    apply (w7_field _ _ 34 (pp + off + kz) _ 0 1 0 1 0 1 (SOff 35 0) (bv_unsigned x) HR0);
      [ rewrite !ew_ewset_other by lia; rewrite E34; apply unsigned_lit_small; lia
      | left; reflexivity
      | apply (w10_den_atom _ 35); rewrite !ew_ewset_other by lia; exact E35
      | cbn; lia | cbn; lia ]. }
  pose proof (w7_regs_kept _ _ ms regs2 _ (w_H W2)
    [Z_to_bv 5 5; Z_to_bv 5 10; Z_to_bv 5 11; Z_to_bv 5 12; Z_to_bv 5 13; Z_to_bv 5 15; Z_to_bv 5 16;
     Z_to_bv 5 17; Z_to_bv 5 20] HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as RK.
  assert (RK20 : getr (ms_regs ms) (Z_to_bv 5 20) = getr regs2 (Z_to_bv 5 20)).
  { rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms (Z_to_bv 5 20) HS). w10_sr_eval.
    rewrite (w10_den_sh _ 21 23 (pp + 0x4000));
      [symmetry; exact P20 | rewrite !ew_ewset_other by lia; exact E21 | exact Hpp47
      | rewrite !ew_ewset_other by lia; exact E23]. }
  assert (Hregs : forall n : Z, In n [2; 3; 4; 8; 9; 19; 23; 21; 27; 25; 20; 26] ->
    getr (ms_regs ms) (Z_to_bv 5 n) = getr regs2 (Z_to_bv 5 n)).
  { intros n Hn. cbn [In] in Hn.
    repeat (destruct Hn as [<-|Hn];
      [first [exact RK20 | (apply RK; [vm_compute; discriminate | apply w10_notin; vm_compute; reflexivity])] |]).
    destruct Hn. }
  assert (R13 : getr (ms_regs ms) (Z_to_bv 5 13) = w64 (Z.of_nat (S kk))).
  { rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms (Z_to_bv 5 13) HS). w10_sr_eval.
    rewrite (w10_den_off _ 13 kz 1) by (rewrite !ew_ewset_other by lia; exact E13).
    f_equal. unfold kz. lia. }
  assert (R12 : getr (ms_regs ms) (Z_to_bv 5 12) = w64 (cnt - Z.of_nat (S kk))).
  { rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms (Z_to_bv 5 12) HS). w10_sr_eval.
    rewrite (w10_den_off _ 12 (cnt - kz) (-1)) by (rewrite !ew_ewset_other by lia; exact E12).
    f_equal. unfold kz. lia. }
  assert (R14 : getr (ms_regs ms) (Z_to_bv 5 14) = w64 off).
  { rewrite RK; [exact P14 | vm_compute; discriminate | apply w10_notin; vm_compute; reflexivity]. }
  assert (R10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (rs_cur rsegs cx rest r1)).
  { rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms (Z_to_bv 5 10) HS). w10_sr_eval.
    rewrite (w10_den_off _ 10 cur 1) by (rewrite !ew_ewset_other by lia; exact E10).
    f_equal. unfold cur, rs_cur. cbn [length]. lia. }
  assert (R15 : getr (ms_regs ms) (Z_to_bv 5 15) = w64 (Z.of_nat (length r1))).
  { rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms (Z_to_bv 5 15) HS). w10_sr_eval.
    rewrite (w10_den_off _ 15 (Z.of_nat (length (x :: r1))) (-1)) by (rewrite !ew_ewset_other by lia; exact E15).
    f_equal. cbn [length]. lia. }
  rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
  apply (HR1 ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ sh ps r1 off bs cnt).
  apply (w10c_finish_R cx rest kk ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ sh ps off bs cnt (x :: r1) r1 x
    HP HRc HJ ltac:(eapply same_io_trans; apply RPgCfgChanges.same_io_wvb) Hregs HKAB Hv Hsk Hsuf' R13 R12 R14 R10 R15).
  unfold kz in *. lia.
- (* a2 - 1 = 0: the count is done *)
  aj_run_to_tok w10_tbl_ok HS HJ SHOK W10Bspan 0x82094.
  { cbn [ss_mem add_cond].
    eapply (w10_awr_cons_pp _ _ _ _ _ _ _ _ _ _ 34%nat (pp + off + kz) pp);
      [reflexivity | | exact Hinp | exact Hfresh | cbn; lia | cbn; unfold PP_SIZE; lia |].
    { rewrite ?ew_ewset_other by lia. rewrite E34. apply unsigned_lit_small. lia. }
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  rewrite branch_ne_U in Hc. rewrite (U_atom_off _ 12 (cnt - kz) (-1)) in Hc;
    [| rewrite !ew_ewset_other by lia; exact E12 | lia | lia].
  rewrite U_lit in Hc by lia.
  apply negb_false_iff, Z.eqb_eq in Hc.

  assert (HKAB : forall a, 0 <= a < 2 ^ 64 -> a <> pp + off + kz ->
    aview rsegs (w_H W2) (ms_mem ms) a = aview rsegs (w_H W2) mem2 a).
  { intros a Ha Hn. transitivity (aview rsegs (w_H W2) (ms_mem msA) a).
    - apply (w10_frame_kept _ _ _ _ _ HFr a Ha). intros (rg & Hr & Hrb). cbn [ss_mem add_cond] in Hr.
      destruct Hr as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb; [|lia|lia].
      rewrite !ew_ewset_other in Hrb by lia. rewrite E34, unsigned_lit_small in Hrb by lia. apply Hn. lia.
    - apply (w10_frame_kept _ _ _ _ _ HFra a Ha). intros (rg & Hr & Hrb). cbn [ss_mem] in Hr.
      destruct Hr as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb; [|lia|lia].
      rewrite E34, unsigned_lit_small in Hrb by lia. apply Hn. lia. }
  assert (Hv : val_mem rsegs (mrestrict (w_H W2) (ms_mem ms)) (pp + off + kz) 1 (bv_unsigned x)).
  { pose proof (w7_region_nth _ _ _ 0 _ HS eq_refl) as HR0.
    replace (pp + off + kz) with (pp + off + kz + 0) by lia.
    apply (w7_field _ _ 34 (pp + off + kz) _ 0 1 0 1 0 1 (SOff 35 0) (bv_unsigned x) HR0);
      [ rewrite !ew_ewset_other by lia; rewrite E34; apply unsigned_lit_small; lia
      | left; reflexivity
      | apply (w10_den_atom _ 35); rewrite !ew_ewset_other by lia; exact E35
      | cbn; lia | cbn; lia ]. }
  pose proof (w7_regs_kept _ _ ms regs2 _ (w_H W2)
    [Z_to_bv 5 5; Z_to_bv 5 10; Z_to_bv 5 11; Z_to_bv 5 12; Z_to_bv 5 13; Z_to_bv 5 15; Z_to_bv 5 16;
     Z_to_bv 5 17; Z_to_bv 5 20] HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as RK.
  assert (RK20 : getr (ms_regs ms) (Z_to_bv 5 20) = getr regs2 (Z_to_bv 5 20)).
  { rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms (Z_to_bv 5 20) HS). w10_sr_eval.
    rewrite (w10_den_sh _ 21 23 (pp + 0x4000));
      [symmetry; exact P20 | rewrite !ew_ewset_other by lia; exact E21 | exact Hpp47
      | rewrite !ew_ewset_other by lia; exact E23]. }
  assert (Hregs : forall n : Z, In n [2; 3; 4; 8; 9; 19; 23; 21; 27; 25; 20; 26] ->
    getr (ms_regs ms) (Z_to_bv 5 n) = getr regs2 (Z_to_bv 5 n)).
  { intros n Hn. cbn [In] in Hn.
    repeat (destruct Hn as [<-|Hn];
      [first [exact RK20 | (apply RK; [vm_compute; discriminate | apply w10_notin; vm_compute; reflexivity])] |]).
    destruct Hn. }
  assert (Hbs : length bs = S kk) by (unfold kz in *; lia).
  rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
  apply (HRT ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ sh ps off bs r1).
  exact (w10c_finish_RT cx rest kk ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ sh ps off bs cnt (x :: r1) r1 x
    HP HRc HJ ltac:(eapply same_io_trans; apply RPgCfgChanges.same_io_wvb) Hregs HKAB Hv Hsk Hsuf' Hbs).
Qed.
End c.
Print Assumptions w10_corr.
