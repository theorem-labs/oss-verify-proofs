(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YI08.v:162-174, 176-180;
   projects/cgif/cgif_file_fuzzer/proofs/lib/YN13.v:121-125; projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC1n.v:201-203, for
   libreac/fuzz_identity's asan-ubsan build (lib/B). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput_seg_D1.v, with its addresses changed; 803 of its 948 lines of code are new or changed and 5920 lines of the source are left out. *)
(* Segment J of LLVMFuzzerTestOneInput's build-B walk (fuzz_identity.asan-ubsan): the piece +0x1748 .. +0x17e8
   (0x81ebc .. 0x81f5c), from the cut jc6 to the cut jc7 of lib/B/Prog/LLVMFuzzerTestOneInput_seg_J_pre.v
   (j_lit1_glue_stmt).
     0x81ebc .. 0x81ed0  x11 = 0, x13 = &exp_dp + ld, x16 = 32 (the first byte of " ("), x14 = the literal
                         (object 9), x15 = 2; then the loop head 0x81ed4 with i = 0 (j_lit1_stmt, a premise)
     0x81f3c, 0x81f40    x11 = ld + 2, stored in mf+200
     0x81f44 .. 0x81f54  put_dec (b = &exp_dp, p = mf+200, v = mf+176 = t_in, mn = 1)
     0x81f58             x6 = mf+168, the shadow base
   The three runs are plain runs (no checked access); the call is put_dec's caller-journal contract. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI08 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentBase IdentRo YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_seg_J_loops_stmt.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require LLVMFuzzerTestOneInput_seg_J_model.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require put_dec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Rt Require Import StrlenDef StrcmpDef MemchrDef SetShadowDef.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import LLVMFuzzerTestOneInput_seg_J_pre.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require put_dec_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* The symbolic states of the three runs. Run 0 (+0x1748, 0x81ebc .. the loop head 0x81ed4): no memory. Run 1
   (+0x17c8, 0x81f3c .. the call at 0x81f54): the machine frame (base s1, atom 9) with mf+176 = t_in (atom 32),
   writable on the counter mf+200 .. mf+207. Run 2 (+0x17e4, 0x81f58 .. 0x81f5c): mf+168 = the shadow base
   (atom 32), read-only. *)
Definition ss_jl10 : sstate := mkSS 0x1748 sr_atoms [] None (mkFacts [] [] []).
Definition jl1_r1 : YP09.region := YP09.mkRegion (Some 9%nat) 176 208 200 208
[YP09.mkChunk 176 (CVal 8 (SOff 32 0))].
Definition ss_jl1a : sstate := mkSS 0x17c8 sr_atoms [jl1_r1] None (mkFacts [] [] []).
Definition jl1_r2 : YP09.region := YP09.mkRegion (Some 9%nat) 168 176 168 168
[YP09.mkChunk 168 (CVal 8 (SOff 32 0))].
Definition ss_jl1b : sstate := mkSS 0x17e4 sr_atoms [jl1_r2] None (mkFacts [] [] []).

(* Membership in a literal register list, without tauto (whose proof term would mention unrelated section
   variables of arrow type). *)
Ltac jl1_in := repeat (first [apply in_eq | apply in_cons]).

(* ---- the model ---------------------------------------------------------------------------------------------- *)
Lemma jl1_lit_bytes : map (fun b : byte => bv_unsigned b) (j_lit_paren ++ [RcIdentModel.zb 0]) = [32; 40; 0].
Proof. vm_compute. reflexivity. Qed.
Lemma jl1_lit_nonul : ~ In (RcIdentModel.zb 0) j_lit_paren.
Proof.
apply LLVMFuzzerTestOneInput_seg_J_model.m2_NZ_notin, LLVMFuzzerTestOneInput_seg_J_model.m2_NZ_b.
vm_compute. reflexivity.
Qed.
Lemma jl1_lit_len : length j_lit_paren = 2%nat.
Proof. reflexivity. Qed.
Lemma jl1_nth0 : bv_unsigned (nth (Z.to_nat 0) j_lit_paren (RcIdentModel.zb 0)) = 32.
Proof. vm_compute. reflexivity. Qed.
Lemma jl1_dp2 : forall inp, j_dp2 inp = (j_dp1 inp ++ j_lit_paren) ++ IdentSpec.DEC (SlotModel.t_in inp) 1.
Proof. intro inp. unfold j_dp2. rewrite app_assoc. reflexivity. Qed.
Lemma jl1_m8 : forall a, a mod 32 = 0 -> (a + 200) mod 8 = 0.
Proof.
intros a Ha. apply Z.mod_divide in Ha; [|lia]. apply Z.mod_divide; [lia|]. destruct Ha as [p ->].
exists (4 * p + 25). ring.
Qed.
Lemma jl1_dec_pos : forall v mn, 1 <= put_dec_c.dec_len v mn.
Proof.
intros v mn. unfold put_dec_c.dec_len, IdentSpec.DEC. rewrite length_app.
assert (H : (1 <= length (IdentSpec.dec_digits (S (Z.to_nat (Z.log2 v))) v))%nat).
{ cbn [IdentSpec.dec_digits]. rewrite length_app. cbn [length]. lia. }
lia.
Qed.
Lemma jl1_sh_off : forall SF c, SF mod 8 = 0 -> shadow_of_addr SHADOW_OFF (SF + c) = SHADOW_OFF + SF / 8 + c / 8.
Proof.
intros SF c H. unfold shadow_of_addr. rewrite <- Z.add_assoc. f_equal.
rewrite (Z.div_mod SF 8) at 1 by lia. rewrite H, Z.add_0_r.
replace (8 * (SF / 8) + c) with (c + (SF / 8) * 8) by lia. rewrite Z.div_add by lia. lia.
Qed.
(* A range inside a zero-shadow range is addressable. *)
Lemma jl1_ra : forall (rdr : reader) lo len x n, zero_shadow rdr SHADOW_OFF lo len -> lo mod 8 = 0 ->
  len mod 8 = 0 -> lo <= x -> x + n <= lo + len -> range_addressable rdr SHADOW_OFF x n.
Proof.
intros rdr lo len x n Hz H8 HL8 Hx Hxn y Hy. exists 0. split; [|left; reflexivity].
replace (shadow_of_addr SHADOW_OFF y) with (shadow_of_addr SHADOW_OFF lo + (y / 8 - lo / 8))
  by (unfold shadow_of_addr; lia).
apply Hz. clear Hz. lia.
Qed.
Lemma jl1_zsh : forall (rdr : reader) lo len x n, zero_shadow rdr SHADOW_OFF lo len -> 0 <= lo ->
  lo + 64 <= x -> 0 < n -> x + n + 96 <= lo + len ->
  range_addressable rdr SHADOW_OFF x n /\ shadow_hull_vis rdr x n.
Proof.
intros rdr lo len x n Hz Hlo Hx Hn Hxn. unfold zero_shadow in Hz. split.
- intros y Hy. exists 0. split; [|left; reflexivity].
  replace (shadow_of_addr SHADOW_OFF y) with (shadow_of_addr SHADOW_OFF lo + (y / 8 - lo / 8))
    by (unfold shadow_of_addr; lia).
  apply Hz. clear Hz. lia.
- intros s Hs. unfold shadow_addr in Hs.
  replace s with (shadow_of_addr SHADOW_OFF lo + (s - SHADOW_OFF - lo / 8)) by (unfold shadow_of_addr; lia).
  rewrite Hz; [discriminate|]. clear Hz. unfold SHADOW_OFF in *. lia.
Qed.

(* When r = 0 the three heap buffers hold their strings with the NUL: each fits its capacity. *)
Module JL1M.
Import RcIdentModel SlotModel IdentSpec.
Lemma has_dash_len : forall l, has_dash l = true -> (1 <= length l)%nat.
Proof. intros [|b l] H; [discriminate | cbn; lia]. Qed.
Lemma tok_go_len : forall l d,
  length (tok_go d l) = (length l - (if negb d && has_dash l then 1 else 0))%nat.
Proof.
induction l as [|b l IH]; intros d; [cbn; destruct d; reflexivity|].
cbn [tok_go has_dash existsb length].
destruct d; cbn [negb andb].
- cbn [length]. rewrite IH. cbn [negb andb]. lia.
- destruct (bz b =? 45) eqn:E; cbn [orb].
  + rewrite IH. cbn [negb andb]. destruct (has_dash l); lia.
  + cbn [length]. rewrite IH. cbn [negb andb]. fold (has_dash l).
    destruct (has_dash l) eqn:Hd; [pose proof (has_dash_len l Hd); lia | lia].
Qed.
Lemma n_r_zero : forall inp, n_r inp = 0 -> n_wok inp = true /\ n_fits inp = true.
Proof.
intros inp H. unfold n_r in H. destruct (n_wok inp), (n_fits inp); cbn in H; try discriminate; split; reflexivity.
Qed.
Lemma bytes_lens : forall inp, n_r inp = 0 ->
  Z.of_nat (length (n_EXP_NM inp ++ [zb 0])) <= t_cap_name inp /\
  Z.of_nat (length (n_TK inp ++ [zb 0])) <= t_cap_tok inp /\
  Z.of_nat (length (n_EXP_DP inp ++ [zb 0])) <= t_cap_disp inp.
Proof.
intros inp H. destruct (n_r_zero inp H) as [_ Hf]. unfold n_fits in Hf.
apply andb_true_iff in Hf as [Hf H3]. apply andb_true_iff in Hf as [H1 H2].
apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. apply Z.ltb_lt in H3.
unfold n_ln, n_lt, n_ld in H1, H2, H3.
assert (LT : length (n_TK inp) = (length (n_EXP_NM inp) - (if has_dash (n_EXP_NM inp) then 1 else 0))%nat)
  by (unfold n_TK, TOK; rewrite tok_go_len; reflexivity).
rewrite !length_app. cbn [length]. rewrite LT.
pose proof (has_dash_len (n_EXP_NM inp)) as HL.
unfold n_ln in H2.
revert H2 HL. destruct (has_dash (n_EXP_NM inp)); intros H2 HL; [specialize (HL eq_refl)|]; lia.
Qed.
End JL1M.

Lemma jl1_pres : forall (r r' : bvmap 5 word), aregs_preserved r r' ->
  forall x, In x [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 21%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] ->
  getr r' x = getr r x.
Proof.
intros r r' H x Hx. cbn [In] in Hx.
destruct Hx as [<-|Hx]; [apply (H 2); unfold acallee_saved; lia|].
destruct Hx as [<-|Hx]; [apply (H 3); unfold acallee_saved; lia|].
destruct Hx as [<-|Hx]; [apply (H 4); unfold acallee_saved; lia|].
destruct Hx as [<-|Hx]; [apply (H 8); unfold acallee_saved; lia|].
destruct Hx as [<-|Hx]; [apply (H 9); unfold acallee_saved; lia|].
destruct Hx as [<-|Hx]; [apply (H 18); unfold acallee_saved; lia|].
destruct Hx as [<-|Hx]; [apply (H 21); unfold acallee_saved; lia|].
destruct Hx as [<-|Hx]; [apply (H 23); unfold acallee_saved; lia|].
destruct Hx as [<-|Hx]; [apply (H 24); unfold acallee_saved; lia|].
destruct Hx as [<-|Hx]; [apply (H 25); unfold acallee_saved; lia|].
destruct Hx as [<-|Hx]; [apply (H 26); unfold acallee_saved; lia|].
destruct Hx as [<-|Hx]; [apply (H 27); unfold acallee_saved; lia|].
destruct Hx.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Variable G : list (Z * Z).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
(* The contract's hypotheses this piece uses that its statement does not carry, with the contract's text
   (lib/B/Prog/LLVMFuzzerTestOneInput.v; HRO and HIMG as LLVMFuzzerTestOneInput_seg_J_pre.v states them for
   j_img): the literal's bytes (llvmf_img) and the fds / fs after the put_dec call (AJ_NIL_IO). *)
Hypothesis HRO : forall rdr, arodata_okS SEGS B RLO RHI rdr -> arodata_okP SEGS pa_relro_lo pa_relro_hi B rdr.
Hypothesis HIMG : forall (W : world SEGS) mem,
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> llvmf_img B G W mem.
Hypothesis AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
m_fds md' = m_fds md /\ m_fs md' = m_fs md.

#[local] Notation ACUT := (acut B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation ECOMMON := (ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation EPRE := (e_pre B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation JKEEP := (jkeep B).
#[local] Notation JC6 := (jc6 B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation JC7 := (jc7 B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation AJ g pos lyc Sc W mem md k := (ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g)
  (e_mem g) (e_md g) [(4, pos)] lyc Sc W mem md k).

(* The loop's head cut with i = 0 (j_lit1_stmt's premise) and its exit cut (j_lit1_stmt's conclusion). *)
Definition jl1_hd (g : ectx) (pos mf nm tk dp : Z) : world SEGS -> config -> Prop :=
ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 7) (BASE + 0x1760)
(fun ly2 S2 W2 regs2 mem2 md2 =>
j_lit_pre B g pos mf nm tk dp (VAL (A_OBJ 9)) j_lit_paren
(j_dp1 (e_pl g) ++ firstn (Z.to_nat 0) j_lit_paren) ly2 S2 W2 regs2 mem2 /\
0 <= 0 < 2 /\
getr regs2 11 = w64 0 /\
getr regs2 12 = w64 (j_L1 (e_pl g)) /\
getr regs2 13 = w64 (SFa g pos + V_dp + j_L1 (e_pl g)) /\
getr regs2 14 = w64 (VAL (A_OBJ 9)) /\
getr regs2 15 = w64 2 /\
getr regs2 16 = w64 (bv_unsigned (nth (Z.to_nat 0) j_lit_paren (RcIdentModel.zb 0)))).
Definition jl1_ex (g : ectx) (pos mf nm tk dp : Z) : world SEGS -> config -> Prop :=
ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 7) (BASE + 0x17c8)
(fun ly2 S2 W2 regs2 mem2 md2 =>
JKEEP g pos mf nm tk dp ly2 S2 W2 regs2 mem2 /\
jdp_regs g pos regs2 /\ jdp_mem g pos W2 mem2 (j_dp1 (e_pl g) ++ j_lit_paren) /\
bytes_at8 W2 mem2 (SFa g pos + V_nm) (SlotModel.n_EXP_NM (e_pl g) ++ [RcIdentModel.zb 0]) /\
getr regs2 27 = w64 (SlotModel.n_ln (e_pl g)) /\
getr regs2 11 = w64 2 /\
getr regs2 12 = w64 (j_L1 (e_pl g))).

(* ---- geometry ----------------------------------------------------------------------------------------------- *)
Lemma jl1_geo0 : AR_laws SEGS B -> STK_LLVMF <= LLVMF_STK ->
  forall (g : ectx) pos mf lyc Sc (W : world SEGS) mem md k,
  AJ g pos lyc Sc W mem md k -> frames Sc = [(4, pos)] -> e_sp0 g - 336 <= mf ->
  frame_addr lyc 4 pos = SFa g pos /\ 4096 <= SFa g pos /\ SFa g pos + 1024 <= alloc_ceiling /\
  in_app (SFa g pos) 1024 /\ alloc_ceiling <= mf - 2 * ESTACK /\ e_sp0 g mod 16 = 0 /\ e_sp0 g <= 2 ^ 47 /\
  2 * ESTACK + 336 <= LLVMF_STK /\ alloc_ceiling <= ly_stk_lo lyc /\ ly_stk_lo lyc + LLVMF_STK <= e_sp0 g /\
  e_sp0 g <= ly_stk_hi lyc.
Proof.
intros LAWS HSTK g pos mf lyc Sc W mem md k HJ Hfrs Hmf.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
destruct Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
destruct Hly as (_ & _ & _ & _ & _ & EF0 & _ & _ & _ & Eslo & Eshi & _).
assert (EF : frame_addr lyc 4 pos = SFa g pos).
{ unfold SFa, frame_addr. rewrite EF0. reflexivity. }
assert (Hin : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc W mem md 4 pos HAR Hin) as (F1 & F2 & F3).
rewrite EF in F1, F2, F3. change (fs_frame_bytes 4) with 1024 in F2, F3.
pose proof HSTK as HS. unfold STK_LLVMF, ASTACK in HS. unfold ESTACK.
clear HJ HAR Hin Hfrs EF0.
split; [exact EF|]. split; [lia|]. split; [lia|]. split; [exact F3|]. split; [lia|]. split; [exact Hal16|].
split; [lia|]. split; [lia|]. split; [lia|]. split; lia.
Qed.

(* Where the entry's frame, its shadow and the machine frame lie, from the journal at any state of the walk. *)
Lemma jl1_geo : AR_laws SEGS B -> STK_LLVMF <= LLVMF_STK ->
  forall (g : ectx) pos mf lyc Sc (W : world SEGS) mem md k,
  AJ g pos lyc Sc W mem md k -> frames Sc = [(4, pos)] -> e_sp0 g - 336 <= mf <= e_sp0 g - 320 ->
  frame_addr lyc 4 pos = SFa g pos /\ 4096 <= SFa g pos /\ SFa g pos + 1024 <= alloc_ceiling /\
  in_app (SFa g pos) 1024 /\ SFa g pos mod 64 = 0 /\
  alloc_ceiling + 16384 <= mf /\ e_sp0 g <= 2 ^ 47 /\ e_sp0 g - LLVMF_STK <= mf - 16384 /\
  0 <= shadow_addr (SFa g pos) /\ shadow_addr (SFa g pos) + 128 <= alloc_ceiling /\
  (SFa g pos + 1024 <= shadow_addr (SFa g pos) \/ shadow_addr (SFa g pos) + 128 <= SFa g pos).
Proof.
intros LAWS HSTK g pos mf lyc Sc W mem md k HJ Hfrs Hmf.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
destruct Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
destruct Hly as (_ & _ & _ & _ & _ & EF0 & _).
assert (EF : frame_addr lyc 4 pos = SFa g pos).
{ unfold SFa, frame_addr. rewrite EF0. reflexivity. }
assert (Hin : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc W mem md 4 pos HAR Hin) as (F1 & F2 & F3).
destruct (frame_al64 SEGS B lyc Sc W mem md 4 pos HAR Hin) as (F64 & _ & _).
rewrite EF in F1, F2, F3, F64. change (fs_frame_bytes 4) with 1024 in F2, F3.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Esh : shadow_addr (SFa g pos) = SHADOW_OFF + SFa g pos / 8) by reflexivity.
pose proof HSTK as HS. unfold STK_LLVMF, ASTACK in HS.
clear HJ HAR Hin Hfrs EF0.
split; [exact EF|]. split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F64|].
split; [clear - Hceil Hslo HS Hmf; lia|]. split; [clear - Hshi H47; lia|]. split; [clear - HS Hmf; lia|].
split; [clear - Esh F1 F2 C1; unfold SHADOW_OFF in Esh; lia|].
split; [clear - Esh F1 F2 C1; unfold SHADOW_OFF in Esh; lia|].
clear - Esh F1 F2 F3 C1.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
destruct F3 as (_ & [Hlo | [Hhi1 Hhi2]]); [left | right]; lia.
Qed.

Lemma jl1_twr_fr : AR_laws SEGS B -> STK_LLVMF <= LLVMF_STK ->
  forall (g : ectx) pos mf lyc Sc (W : world SEGS) mem md k sp q n,
  AJ g pos lyc Sc W mem md k -> frames Sc = [(4, pos)] -> e_sp0 g - 336 <= mf -> mf <= sp ->
  SFa g pos <= q -> q + n <= SFa g pos + 1024 ->
  twr_ok B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) lyc Sc [(4, pos)] W mem sp q n.
Proof.
intros LAWS HSTK g pos mf lyc Sc W mem md k sp q n HJ Hfrs Hmf Hsp Hq1 Hq2 a Ha.
destruct (jl1_geo0 LAWS HSTK g pos mf lyc Sc W mem md k HJ Hfrs Hmf) as (EF & G1 & G2 & G3 & G4 & _).
assert (Hw : awr_byte LLVMF_STK (e_sp0 g) [] (ablocks B (e_ly g) (e_S g)) (ablocks B lyc Sc) lyc [(4, pos)] a).
{ right. right. right. exists 4, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. rewrite EF.
  change (fs_frame_bytes 4) with 1024. lia. }
destruct (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) as [Hp Ho].
clear HJ.
split; [exact Hw|]. split; [exact Hp|]. split; [exact Ho|]. unfold ESTACK in *. lia.
Qed.

Lemma jl1_stk : AR_laws SEGS B -> STK_LLVMF <= LLVMF_STK ->
  forall (g : ectx) pos mf lyc Sc (W : world SEGS) mem md k q n,
  AJ g pos lyc Sc W mem md k -> frames Sc = [(4, pos)] -> e_sp0 g - 336 <= mf ->
  mf <= q -> 0 < n -> q + n + 96 <= e_sp0 g ->
  twr_ok B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) lyc Sc [(4, pos)] W mem mf q n /\
  tsrc_ok W mem mf q n.
Proof.
intros LAWS HSTK g pos mf lyc Sc W mem md k q n HJ Hfrs Hmf Hq Hn Hqn.
destruct (jl1_geo0 LAWS HSTK g pos mf lyc Sc W mem md k HJ Hfrs Hmf)
  as (EF & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by reflexivity.
pose proof (al_zshadow _ _ LAWS lyc Sc W mem md (ly_stk_lo lyc, ly_stk_hi lyc - ly_stk_lo lyc) HAR
  ltac:(left; reflexivity)) as HZ.
cbn [fst snd] in HZ.
destruct (jl1_zsh (aview SEGS (w_H W) mem) (ly_stk_lo lyc) (ly_stk_hi lyc - ly_stk_lo lyc) q n HZ
  ltac:(lia) ltac:(lia) Hn ltac:(lia)) as [HRA HHV].
assert (Hw : forall a, q <= a < q + n ->
  awr_byte LLVMF_STK (e_sp0 g) [] (ablocks B (e_ly g) (e_S g)) (ablocks B lyc Sc) lyc [(4, pos)] a).
{ intros a Ha. left. lia. }
split.
- intros a Ha. destruct (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ (Hw a Ha)) as [Hp Ho].
  split; [exact (Hw a Ha)|]. split; [exact Hp|]. split; [exact Ho|]. lia.
- split; [intros a Ha; split; [apply aview_some_of_apresent; apply Hpres; lia | lia]|].
  split; [exact HRA|]. split; [exact HHV|].
  split; [right; lia|]. lia.
Qed.

(* put_dec at 0x81f54: b = exp_dp (SF+592), p = mf+200 holding n, v = t_in, mn = 1, the 64 bytes of exp_dp
   addressable (0x81b78 .. 0x81ba4 cleared their shadow). *)
Lemma jl1_pd : AR_laws SEGS B -> identb_prog_sig_ok (PI := PI) -> put_dec.tput_dec_spec B ->
  STK_LLVMF <= LLVMF_STK -> EV_LLVMF <= EV_LIB ->
  forall (g : ectx) (pos mf : Z) (W : world SEGS) (regs : bvmap 5 word) mem md lyc Sc k n v retk,
  EPRE g -> AJ g pos lyc Sc W mem md k -> frames Sc = [(4, pos)] -> 0 <= k <= EV_LLVMF ->
  e_sp0 g - 336 <= mf <= e_sp0 g - 320 -> mf mod 32 = 0 ->
  getr regs 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  getr regs 2 = w64 mf -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 (SFa g pos + V_dp) -> getr regs 11 = w64 (mf + M_n2) ->
  getr regs 12 = w64 v -> getr regs 13 = w64 1 -> 0 <= v < 256 ->
  0 <= n -> n + put_dec_c.dec_len v 1 <= N_dp ->
  val_mem SEGS (rd W mem) (mf + M_n2) 8 n ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (SFa g pos + V_dp) N_dp ->
  SRr SEGS W (cfg_at SEGS (SIGMA IB_put_dec) regs mem md)
    (put_dec.tput_dec_post B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
       lyc Sc W mem k regs (SFa g pos + V_dp) (mf + M_n2) n v 1).
Proof.
intros LAWS PSIG HPD HSTK HEV g pos mf W regs mem md lyc Sc k n v retk HEP HJ Hfrs Hk Hmf Hmf32 R1 Hrk Hrk2
  R2 R3 R4 R10 R11 R12 R13 Rv Hn Hlen HVM HRA.
destruct (jl1_geo0 LAWS HSTK g pos mf lyc Sc W mem md k HJ Hfrs (proj1 Hmf))
  as (EF & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
pose proof asan_consts as (C1 & _). pose proof pa_B_ok as HBASE. pose proof (pa_base_lo (PL := PL_identb)) as HBLO.
pose proof (jl1_dec_pos v 1) as HD.
assert (HES : ESTACK = 4096) by reflexivity.
assert (HPS : put_dec.PUT_DEC_STK = 4208) by reflexivity.
assert (Hsp : spZ regs = mf) by (unfold spZ; rewrite R2; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (Hsig : SIGMA IB_put_dec = BASE + AF_put_dec) by (apply PSIG; reflexivity).
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
destruct HEP as (_ & _ & _ & _ & _ & _ & _ & _ & Hev0 & _).
destruct (jl1_stk LAWS HSTK g pos mf lyc Sc W mem md k (mf + M_n2) 8 HJ Hfrs (proj1 Hmf)
  ltac:(unfold M_n2; lia) ltac:(lia) ltac:(unfold M_n2; lia)) as [WP SP].
assert (WB : twr_ok B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) lyc Sc [(4, pos)] W mem mf
  (SFa g pos + V_dp + n) (put_dec_c.dec_len v 1)).
{ apply (jl1_twr_fr LAWS HSTK g pos mf lyc Sc W mem md k mf); [exact HJ | exact Hfrs | exact (proj1 Hmf) | lia | |];
  unfold V_dp, N_dp in *; lia. }
assert (SB : tsrc_ok W mem mf (SFa g pos + V_dp + n) (put_dec_c.dec_len v 1)).
{ split; [intros a Ha; split; [apply aview_some_of_apresent; exact (proj1 (proj2 (WB a Ha))) | unfold V_dp, N_dp in *; lia]|].
  split; [eapply range_addressable_sub; [exact HRA | unfold V_dp, N_dp in *; lia | unfold V_dp, N_dp in *; lia]|].
  split.
  { apply (shadow_hull_vis_of_frame SEGS B LAWS lyc Sc W mem md 4 pos _ _ (proj1 HJ)
      ltac:(rewrite Hfrs; left; reflexivity));
      [rewrite EF; unfold V_dp; lia | rewrite EF; change (fs_frame_bytes 4) with 1024; unfold V_dp, N_dp in *; lia | lia]. }
  split; [apply (amem_range_sub_app (SFa g pos) 1024 _ _ G3 G2); unfold V_dp, N_dp in *; lia|].
  unfold V_dp, N_dp in *; lia. }
rewrite Hsig.
refine (HPD LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] lyc Sc W mem md k regs
  (SFa g pos + V_dp) (mf + M_n2) n v 1 HJ _ _ R3 R4 R10 R11 _ _ R13 ltac:(lia) _ _ _ _ _ _ _ HVM _ _ _ _ _ _ _ _).
- rewrite R1. apply ret_ok_codeptr_v; [lia | exact Hrk2].
- unfold raZ. rewrite R1, unsigned_lit_small by lia. lia.
- rewrite R12. unfold w64. rewrite unsigned_lit_small by lia. apply Z.mod_small. lia.
- left. rewrite R12. unfold w64. rewrite unsigned_lit_small by lia. lia.
- rewrite Hsp. exact Hmf32.
- rewrite Hsp, HPS. lia.
- rewrite Hsp. lia.
- rewrite Hfrs. cbn [length]. lia.
- unfold M_n2. exact (jl1_m8 mf Hmf32).
- unfold V_dp. lia.
- exact Hn.
- rewrite Hsp. exact WP.
- rewrite Hsp. exact WB.
- rewrite Hsp. exact SP.
- rewrite Hsp. exact SB.
- right. unfold M_n2, V_dp, N_dp in *. lia.
- left. rewrite Hsp. unfold M_n2. lia.
- right. rewrite Hsp, HPS. unfold V_dp, N_dp in *. lia.
- unfold put_dec.EV_PUT_DEC. lia.
Qed.

(* ---- the start states of the three runs ---------------------------------------------------------------------- *)
Lemma jl1_ent0 : forall (W : world SEGS) (regs : bvmap 5 word) mem,
  st_ok_pi SEGS VAL (Eimg (Ereg regs [])) ss_jl10
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x1748)) mem (seg_rom SEGS))).
Proof.
intros W regs mem. rewrite restrict_mkst_fx. unfold ss_jl10. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor.
- exact Logic.I.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [exact Logic.I | split; exact Logic.I].
Qed.

Lemma jl1_ent1 : forall (W : world SEGS) (regs : bvmap 5 word) mem mf ti,
  getr regs 9 = w64 mf -> alloc_ceiling <= mf -> mf + 216 <= 2 ^ 47 -> 0 <= ti < 256 ->
  val_mem SEGS (rd W mem) (mf + 176) 8 ti ->
  (forall o, 200 <= o < 208 -> apresent (w_H W) mem (mf + o)) ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [Z_to_bv 64 ti])) ss_jl1a
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x17c8)) mem (seg_rom SEGS))).
Proof.
intros W regs mem mf ti R9 H1 H2 H3 V176 P1.
pose proof asan_consts as (C1 & _).
set (E := Eimg (Ereg regs [Z_to_bv 64 ti])).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 ti]) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (U9 : bv_unsigned (ew E 9) = mf).
{ rewrite EL by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), R9.
  apply unsigned_lit_small. lia. }
assert (E32 : ew E 32 = Z_to_bv 64 ti) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
rewrite restrict_mkst_fx. unfold ss_jl1a. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor].
  unfold jl1_r1, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U9. split; [lia|]. split; [lia|]. split.
  + intros o Ho. apply (apresent_writable SEGS). apply P1. lia.
  + constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ mf 176 8 (SOff 32 0) ti);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia | exact V176].
- apply pairwise_disjoint_of_extents. unfold jl1_r1, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi zpairwise_disjoint zall_disjoint]. split; exact I.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [exact I | split; exact I].
Qed.

Lemma jl1_ent2 : forall (W : world SEGS) (regs : bvmap 5 word) mem mf,
  getr regs 9 = w64 mf -> alloc_ceiling <= mf -> mf + 216 <= 2 ^ 47 ->
  val_mem SEGS (rd W mem) (mf + 168) 8 SHADOW_OFF ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [Z_to_bv 64 SHADOW_OFF])) ss_jl1b
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x17e4)) mem (seg_rom SEGS))).
Proof.
intros W regs mem mf R9 H1 H2 V168.
pose proof asan_consts as (C1 & _).
set (E := Eimg (Ereg regs [Z_to_bv 64 SHADOW_OFF])).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 SHADOW_OFF]) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (U9 : bv_unsigned (ew E 9) = mf).
{ rewrite EL by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), R9.
  apply unsigned_lit_small. lia. }
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
rewrite restrict_mkst_fx. unfold ss_jl1b. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor].
  unfold jl1_r2, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ mf 168 8 (SOff 32 0) SHADOW_OFF);
  [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; lia | lia | exact V168].
- apply pairwise_disjoint_of_extents. unfold jl1_r2, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi zpairwise_disjoint zall_disjoint]. split; exact I.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [exact I | split; exact I].
Qed.

(* A value a run stored, read off the state after a run that ends in a call. *)
Lemma jl1_chunk : forall E ss ms i r off (n : N) e b v,
  st_ok SEGS E ss ms -> nth_error (ss_mem ss) i = Some r -> base_val E (YP09.r_base r) = b ->
  In (YP09.mkChunk off (CVal n e)) (YP09.r_chunks r) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
  val_mem SEGS (ms_mem ms) (b + off) (N.to_nat n) v.
Proof.
intros E ss ms i r off n e b v HS Hi Hb Hin He Hv Hn.
pose proof (st_ok_region_nth E ss ms i r HS Hi) as (_ & _ & _ & Hc). rewrite Hb in Hc.
apply (val_of_chunk_ok SEGS E (ms_mem ms) b off n e v); [|exact He | exact Hv | exact Hn].
exact (proj1 (Forall_forall _ _) Hc _ Hin).
Qed.

(* ---- a run that writes nothing keeps every fact of the cut ------------------------------------------------ *)
Lemma jl1_ec_moved : forall g pos mf ly2 S2 (W2 : world SEGS) regs2 regs3 mem2 mem3 md2 md3,
ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 ->
mrestrict (w_H W2) mem3 = mrestrict (w_H W2) mem2 ->
(forall r, In r [2%bv; 3%bv; 4%bv; 6%bv; 8%bv; 9%bv; 12%bv; 18%bv; 21%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] ->
getr regs3 r = getr regs2 r) ->
m_fds md3 = m_fds md2 -> m_fs md3 = m_fs md2 ->
ECOMMON g pos mf ly2 S2 W2 regs3 mem3 md3.
Proof.
intros g pos mf ly2 S2 W2 regs2 regs3 mem2 mem3 md2 md3 HC EQR RK Efds Efs.
unfold ecommon, bytes_at8 in *. rewrite EQR, Efds, Efs.
rewrite (RK 2%bv ltac:(jl1_in)), (RK 3%bv ltac:(jl1_in)), (RK 4%bv ltac:(jl1_in)),
(RK 8%bv ltac:(jl1_in)), (RK 9%bv ltac:(jl1_in)).
exact HC.
Qed.
Lemma jl1_jkeep_moved : forall g pos mf nm tk dp ly2 S2 (W2 : world SEGS) regs2 regs3 mem2 mem3,
JKEEP g pos mf nm tk dp ly2 S2 W2 regs2 mem2 ->
mrestrict (w_H W2) mem3 = mrestrict (w_H W2) mem2 ->
(forall r, In r [2%bv; 3%bv; 4%bv; 6%bv; 8%bv; 9%bv; 12%bv; 18%bv; 21%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] ->
getr regs3 r = getr regs2 r) ->
JKEEP g pos mf nm tk dp ly2 S2 W2 regs3 mem3.
Proof.
intros g pos mf nm tk dp ly2 S2 W2 regs2 regs3 mem2 mem3 HK EQR RK.
assert (EQV : aview SEGS (w_H W2) mem3 = aview SEGS (w_H W2) mem2) by (unfold aview; rewrite EQR; reflexivity).
unfold jkeep, sh_reg, id_at, sh_zero, sh_blk, bytes_at8 in *. rewrite EQV, EQR.
rewrite (RK 21%bv ltac:(jl1_in)), (RK 23%bv ltac:(jl1_in)), (RK 24%bv ltac:(jl1_in)).
exact HK.
Qed.
Lemma jl1_jdp_regs_moved : forall g pos regs2 regs3,
jdp_regs g pos regs2 ->
(forall r, In r [2%bv; 3%bv; 4%bv; 6%bv; 8%bv; 9%bv; 12%bv; 18%bv; 21%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] ->
getr regs3 r = getr regs2 r) ->
jdp_regs g pos regs3.
Proof.
intros g pos regs2 regs3 HD RK. unfold jdp_regs in *.
rewrite (RK 6%bv ltac:(jl1_in)), (RK 18%bv ltac:(jl1_in)), (RK 25%bv ltac:(jl1_in)),
(RK 26%bv ltac:(jl1_in)).
exact HD.
Qed.
Lemma jl1_jdp_mem_moved : forall g pos (W2 : world SEGS) mem2 mem3 l,
jdp_mem g pos W2 mem2 l -> mrestrict (w_H W2) mem3 = mrestrict (w_H W2) mem2 -> jdp_mem g pos W2 mem3 l.
Proof.
intros g pos W2 mem2 mem3 l HD EQR.
assert (EQV : aview SEGS (w_H W2) mem3 = aview SEGS (w_H W2) mem2) by (unfold aview; rewrite EQR; reflexivity).
unfold jdp_mem, sh_zero, bytes_at8 in *. rewrite EQV, EQR. exact HD.
Qed.
Lemma jl1_bytes_moved : forall (W2 : world SEGS) mem2 mem3 a l,
bytes_at8 W2 mem2 a l -> mrestrict (w_H W2) mem3 = mrestrict (w_H W2) mem2 -> bytes_at8 W2 mem3 a l.
Proof. intros W2 mem2 mem3 a l H EQR. unfold bytes_at8 in *. rewrite EQR. exact H. Qed.

(* ---- +0x1748 .. +0x1760 (0x81ebc .. 0x81ed4): from jc6 to the loop's head with i = 0 ------------------------ *)
Lemma jl1_head : forall (g : ectx) pos mf nm tk dp (W2 : world SEGS) c2,
  AR_laws SEGS B -> globs_marked SEGS B G -> In (VAL (A_OBJ 9), 3) G ->
  JC6 g pos mf nm tk dp W2 c2 -> SlotModel.n_wok (e_pl g) = true ->
  SRr SEGS W2 c2 (jl1_hd g pos mf nm tk dp).
Proof using RO HRO HIMG.
intros g pos mf nm tk dp W2 c2 LAWS HGM HG9 Hc6 Hwok.
destruct Hc6 as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & Hk & MLE & MOK & HC & HP).
destruct HP as (HK & HDR & HDM & R27 & R12 & HNM).
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  HPRE & _).
pose proof HDR as (_ & _ & _ & R26).
pose proof (SRr_run_to_pi_AJ B LAWS) as RUNTOP.
remember (Eimg (Ereg regs2 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E250 : ew E 250%nat = Z_to_bv 64 (VAL (A_OBJ 9)))
  by (rewrite HE; exact (Eimg_img _ (A_OBJ 9) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))).
assert (AGE : env_agree 32 (Ereg regs2 []) E)
  by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HS : st_ok_pi SEGS VAL E ss_jl10
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x1748)) mem2 (seg_rom SEGS))))
  by (rewrite HE; apply jl1_ent0).
clear HE.
unfold cfg_at. change (w64 (BASE + 0x1748)) with (Z_to_bv 64 (BASE + 0x1748)).
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 (BASE + 0x1748)) mem2 (seg_rom SEGS))) in HJ.
paj_run_to_sh RUNTOP HS HJ 0x1760.
{ cbn [ss_mem ss_jl10]. apply awr_ok_nil. }
cbn [ms_mem mkst] in HF, HFr, HG, HJ.
assert (EQR : mrestrict (w_H W2) (ms_mem ms) = mrestrict (w_H W2) mem2).
{ apply (frame_of_read_only E (ss_mem ss_jl10)); [reflexivity | exact HFr]. }
assert (RK : forall r, In r [2%bv; 3%bv; 4%bv; 6%bv; 8%bv; 9%bv; 12%bv; 18%bv; 21%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] ->
  getr (ms_regs ms) r = getr regs2 r)
  by (eapply (regs_kept_of_st_ok_pi E _ _ regs2 [] _ HS AGE); vm_compute; reflexivity).
prreg HS (11%bv : bv 5) Q11. prreg HS (13%bv : bv 5) Q13. prreg HS (14%bv : bv 5) Q14.
prreg HS (15%bv : bv 5) Q15. prreg HS (16%bv : bv 5) Q16.
rewrite (EE 12%nat 12%bv eq_refl), (EE 26%nat 26%bv eq_refl), R12, R26 in Q13.
unfold w64 in Q13. rewrite alu64_add_lit in Q13.
pose proof (@j_img _ _ _ B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none
  ameta_inv arodata_okS G RO HRO HIMG g pos _ ly2 S2 W2 (ms_mem ms) _ HJ HPRE) as HIM.
unfold llvmf_img in HIM. destruct HIM as (_ & _ & _ & _ & _ & _ & _ & _ & HO9 & _).
pose proof (HGM ly2 S2 W2 (ms_mem ms) _ (VAL (A_OBJ 9)) 3 HG9 (proj1 HJ)) as HBS.
pose proof (pa_obj_img 9 ltac:(lia)) as [Hlo9 Hhi9].
pose proof (LLVMFuzzerTestOneInput_seg_J_model.m1_n_ln_le (e_pl g) Hwok) as HL.
apply SRr_ret. unfold jl1_hd, acut. pmkst HS.
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ =>
  exists ly2, S2, (ms_regs ms), (ms_mem ms), mdx end.
split; [reflexivity|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|].
split; [exact MLE|]. split; [exact MOK|].
split; [apply (jl1_ec_moved g pos mf ly2 S2 W2 regs2 (ms_regs ms) mem2 (ms_mem ms) md2 _ HC EQR RK);
  [apply j_wvb_fds | apply j_wvb_fs]|].
unfold j_lit_pre.
replace (firstn (Z.to_nat 0) j_lit_paren) with (@nil byte) by reflexivity. rewrite app_nil_r.
split.
{ split; [exact (jl1_jkeep_moved g pos mf nm tk dp ly2 S2 W2 regs2 (ms_regs ms) mem2 (ms_mem ms) HK EQR RK)|].
  split; [exact (jl1_jdp_regs_moved g pos regs2 (ms_regs ms) HDR RK)|].
  split; [exact (jl1_jdp_mem_moved g pos W2 mem2 (ms_mem ms) _ HDM EQR)|].
  split; [exact (jl1_bytes_moved W2 mem2 (ms_mem ms) _ _ HNM EQR)|].
  split; [rewrite (RK 27%bv ltac:(jl1_in)); exact R27|].
  split; [exact Hwok|].
  split; [change (Z.of_nat (length j_lit_paren)) with 2;
    change (Z.of_nat (length (j_dp1 (e_pl g)))) with (SlotModel.n_ln (e_pl g)); unfold N_dp; clear - HL; lia|].
  split; [unfold bytes_at8; rewrite jl1_lit_bytes; exact HO9|].
  split; [change (Z.of_nat (length j_lit_paren) + 1) with 3; exact HBS|].
  split; [exact Hlo9|].
  split; [change (Z.of_nat (length j_lit_paren)) with 2; clear - Hhi9; lia|].
  exact jl1_lit_nonul. }
split; [lia|].
split; [exact Q11|].
split; [rewrite (RK 12%bv ltac:(jl1_in)); exact R12|].
split; [rewrite Q13; unfold w64; f_equal; ring|].
split; [rewrite Q14, E250; reflexivity|].
split; [exact Q15|].
rewrite jl1_nth0. exact Q16.
Qed.

(* ---- what a state of the journal keeps of the entry and of the cut before the call ------------------------ *)
(* The input block, from the journal: no entry block is gone (hblocks). *)
Lemma jl1_inp : forall g pos ly3 S3 (W3 : world SEGS) mem3 md3 k hs,
  EPRE g -> AJ g pos ly3 S3 W3 mem3 md3 k -> hblocks B g ly3 S3 hs -> bytes_at8 W3 mem3 (e_p g) (e_pl g).
Proof.
intros g pos ly3 S3 W3 mem3 md3 k hs HPRE HJ (Hperm & _).
unfold e_pre, tLLVMFuzzerTestOneInput_pre in HPRE.
destruct HPRE as (_ & _ & _ & _ & Hinp & Hlen & Hgar & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
destruct Hinp as [[Hn0 _] | [Hn Hpin]].
- unfold bytes_at8. destruct (e_pl g) as [|x l]; [intros j Hj; cbn in Hj; lia | cbn in Hlen; lia].
- unfold bytes_at8. apply (garr8_frame SEGS _ _ (e_p g) _ Hgar). intros a Ha. rewrite length_map in Ha.
  apply (mbyte_of_aview SEGS).
  assert (Hin3 : In (e_p g, e_n g) (ablocks B ly3 S3))
    by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; exact Hpin).
  replace a with (e_p g + (a - e_p g)) by lia.
  apply (F2 (e_p g) (e_n g) (a - e_p g) Hpin Hin3).
  + unfold req_size. destruct (Z.eqb_spec (e_n g) 0); lia.
  + intros (r & Hr & _). destruct Hr.
Qed.

(* ecommon at a later state of the same journal, from the registers and the bytes it states. *)
Lemma jl1_ec_keep : forall g pos mf ly2 S2 (W2 : world SEGS) regs2 mem2 md2 ly3 S3 (W3 : world SEGS) regs3 mem3 md3 k3 hs,
  ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 ->
  AJ g pos ly3 S3 W3 mem3 md3 k3 -> hblocks B g ly3 S3 hs ->
  getr regs3 2 = getr regs2 2 -> getr regs3 9 = getr regs2 9 -> getr regs3 8 = getr regs2 8 ->
  getr regs3 3 = getr regs2 3 -> getr regs3 4 = getr regs2 4 ->
  (forall a, (mf <= a < mf + 200 \/ mf + 208 <= a < e_sp0 g \/ SFa g pos + 1016 <= a < SFa g pos + 1024) ->
    aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) mem2 a) ->
  ECOMMON g pos mf ly3 S3 W3 regs3 mem3 md3.
Proof.
intros g pos mf ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 k3 hs HEC HJ3 HB3 R2 R9 R8 R3 R4 KEEP.
destruct HEC as (Hsp & Hs1 & Hs0 & Hmf & Hmf32 & Hgp & Htp & V16 & V64 & V192 & V168 & Vra & Vs0 & W9 & W18 & W19 &
  W20 & W21 & W22 & W23 & W24 & W25 & W26 & W27 & Vfl & HPRE & Hfds & Hfs & Hinp).
assert (VK : forall a n v, (forall x, a <= x < a + Z.of_nat n ->
    (mf <= x < mf + 200 \/ mf + 208 <= x < e_sp0 g \/ SFa g pos + 1016 <= x < SFa g pos + 1024)) ->
  val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W3 mem3) a n v).
{ intros a n v Hx Hv. eapply (val_mem_kept SEGS); [|exact Hv]. intros kk Hk. apply KEEP. apply Hx. lia. }
destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as [Ifd Ifs].
refine (conj _ (conj _ (conj _ (conj Hmf (conj Hmf32 (conj _ (conj _ _))))))).
- rewrite R2. exact Hsp.
- rewrite R9. exact Hs1.
- rewrite R8. exact Hs0.
- rewrite R3. exact Hgp.
- rewrite R4. exact Htp.
- repeat match goal with
  | |- _ /\ _ => split
  | |- e_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact HPRE
  | |- forall fd, _ => intros fd; rewrite Ifd; reflexivity
  | |- m_fs _ = _ => exact Ifs
  | |- bytes_at8 _ _ (e_p g) _ => exact (jl1_inp g pos ly3 S3 W3 mem3 md3 k3 hs HPRE HJ3 HB3)
  | |- val_mem _ _ ?a _ _ => apply VK; [intros x Hx; cbn in Hx; clear - Hx Hmf; lia | assumption]
  end.
Qed.

(* jkeep at a later state, from the registers it states and the bytes the call and the runs kept. *)
Lemma jl1_jkeep_keep : forall g pos mf nm tk dp ly3 S3 (W3 : world SEGS) regs3 mem3 ly5 S5 (W5 : world SEGS) regs5 mem5,
  JKEEP g pos mf nm tk dp ly3 S3 W3 regs3 mem3 ->
  ablocks B ly5 S5 = ablocks B ly3 S3 ->
  getr regs5 21 = getr regs3 21 -> getr regs5 23 = getr regs3 23 -> getr regs5 24 = getr regs3 24 ->
  SFa g pos mod 64 = 0 -> 0 <= SFa g pos ->
  (forall a, mf + 112 <= a < mf + 192 -> aview SEGS (w_H W5) mem5 a = aview SEGS (w_H W3) mem3 a) ->
  (forall a, SFa g pos + V_id <= a < SFa g pos + V_id + N_id ->
    aview SEGS (w_H W5) mem5 a = aview SEGS (w_H W3) mem3 a) ->
  (forall a, shadow_addr (SFa g pos) <= a < shadow_addr (SFa g pos) + 128 ->
    aview SEGS (w_H W5) mem5 a = aview SEGS (w_H W3) mem3 a) ->
  (forall b m i, In (b, m) (ablocks B ly3 S3) -> 0 <= i < req_size m ->
    aview SEGS (w_H W5) mem5 (b + i) = aview SEGS (w_H W3) mem3 (b + i)) ->
  JKEEP g pos mf nm tk dp ly5 S5 W5 regs5 mem5.
Proof.
intros g pos mf nm tk dp ly3 S3 W3 regs3 mem3 ly5 S5 W5 regs5 mem5
  (Hbl & Hsh & H24 & H21 & V152 & V184 & V144 & V128 & V120 & V176 & V160 & V112 & Hid & Hbufs)
  EB R21 R23 R24 H64 H0 KMF KID KSH KB.
assert (Hsf8 : SFa g pos mod 8 = 0).
{ pose proof (Z.div_mod (SFa g pos) 64 ltac:(lia)) as D. rewrite H64, Z.add_0_r in D. rewrite D.
  replace (64 * (SFa g pos / 64)) with ((8 * (SFa g pos / 64)) * 8) by lia. apply Z_mod_mult. }
assert (VK : forall a (n : nat) v, mf + 112 <= a -> a + Z.of_nat n <= mf + 192 ->
  val_mem SEGS (rd W3 mem3) a n v -> val_mem SEGS (rd W5 mem5) a n v).
{ intros a n v H1 H2 Hv. apply (val_mem_kept SEGS (w_H W3) (w_H W5) mem3 mem5 a n v); [|exact Hv].
  intros kk Hkk. apply KMF. clear - H1 H2 Hkk. lia. }
unfold jkeep.
split; [unfold hblocks in *; rewrite EB; exact Hbl|].
split; [unfold sh_reg in *; rewrite R23; exact Hsh|].
split; [rewrite R24; exact H24|].
split; [rewrite R21; exact H21|].
split; [apply VK; [lia | cbn; lia | exact V152]|].
split; [apply VK; [lia | cbn; lia | exact V184]|].
split; [apply VK; [lia | cbn; lia | exact V144]|].
split; [apply VK; [lia | cbn; lia | exact V128]|].
split; [apply VK; [lia | cbn; lia | exact V120]|].
split; [apply VK; [lia | cbn; lia | exact V176]|].
split; [apply VK; [lia | cbn; lia | exact V160]|].
split; [apply VK; [lia | cbn; lia | exact V112]|].
split.
{ unfold id_at in *. destruct Hid as (Hidb & Hidz & Hidk). split; [|split].
  - unfold bytes_at8 in *. apply (garr8_frame SEGS _ _ _ _ Hidb). intros a Ha. apply (mbyte_of_aview SEGS). apply KID.
    rewrite length_map in Ha. unfold m_id in Ha. rewrite SlotModel.rec_id_length in Ha.
    change (Z.of_nat RcIdentModel.ID_SIZE) with 38 in Ha. unfold N_id. clear - Ha. lia.
  - unfold sh_zero, zero_shadow in *. intros i Hi. rewrite KSH; [exact (Hidz i Hi)|].
    unfold V_id, N_id in *. change (38 / 8) with 4 in Hi. rewrite (jl1_sh_off (SFa g pos) 352 Hsf8).
    change (352 / 8) with 44. unfold shadow_addr. clear - Hi. lia.
  - unfold sh_blk in *. apply (j_block_shadow_moved (aview SEGS (w_H W3) mem3)); [|exact Hidk].
    intros i Hi. apply KSH. unfold V_id, N_id in *. change ((38 + 7) / 8) with 5 in Hi.
    rewrite (jl1_sh_off (SFa g pos) 352 Hsf8). change (352 / 8) with 44. unfold shadow_addr. clear - Hi. lia. }
intros Hr. destruct (Hbufs Hr) as (Bn & Bt & Bd).
destruct (JL1M.bytes_lens (e_pl g) Hr) as (Ln & Lt & Ld).
destruct Hbl as [Hperm _].
assert (BK : forall b m l, In (b, m) [(nm, Z.max (SlotModel.t_cap_name (e_pl g)) 1);
    (tk, Z.max (SlotModel.t_cap_tok (e_pl g)) 1); (dp, Z.max (SlotModel.t_cap_disp (e_pl g)) 1)] ->
  0 <= m -> Z.of_nat (length l) <= m -> bytes_at8 W3 mem3 b l -> bytes_at8 W5 mem5 b l).
{ intros b m l Hin Hm Hl Hb. unfold bytes_at8 in *. apply (garr8_frame SEGS _ _ _ _ Hb). intros a Ha.
  apply (mbyte_of_aview SEGS). rewrite length_map in Ha. pose proof (req_size_pos m Hm) as [_ Hq].
  replace a with (b + (a - b)) by lia.
  apply (KB b m (a - b)); [|clear - Ha Hl Hq; lia].
  apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. left. exact Hin. }
split; [|split].
- apply (BK nm (Z.max (SlotModel.t_cap_name (e_pl g)) 1)); [left; reflexivity | lia | clear - Ln; lia | exact Bn].
- apply (BK tk (Z.max (SlotModel.t_cap_tok (e_pl g)) 1)); [right; left; reflexivity | lia | clear - Lt; lia | exact Bt].
- apply (BK dp (Z.max (SlotModel.t_cap_disp (e_pl g)) 1)); [right; right; left; reflexivity | lia | clear - Ld; lia | exact Bd].
Qed.

(* ---- +0x17c8 .. +0x17e8 (0x81f3c .. 0x81f5c): from the loop's exit to jc7 --------------------------------- *)
Lemma jl1_tail : forall (g : ectx) pos mf nm tk dp (W3 : world SEGS) c3,
  AR_laws SEGS B -> STK_LLVMF <= LLVMF_STK -> EV_LLVMF <= EV_LIB -> put_dec.tput_dec_spec B ->
  identb_prog_sig_ok (PI := PI) -> ameter_laws MT -> (forall s s' : astate, mo_le MT s s' 0) ->
  jl1_ex g pos mf nm tk dp W3 c3 -> SlotModel.n_wok (e_pl g) = true ->
  SRr SEGS W3 c3 (JC7 g pos mf nm tk dp).
Proof using AJ_NIL_IO.
intros g pos mf nm tk dp W3 c3 LAWS HSTK HEV HPD PSIG MTL HMT0 Hex Hwok.
pose proof (SRr_run_pi_AJ B LAWS) as RUNP. pose proof (SRr_run_pi_AJ_call B LAWS) as RUNC.
pose proof (SRr_run_to_pi_AJ B LAWS) as RUNTOP.
destruct Hex as (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ & Hfrs & Hk & MLE & MOK & HC & HP).
destruct HP as (HK & HDR & HDM & HNM & R27 & R11 & R12).
pose proof HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & _ & _ & _ & V168 & _ & _ &
  _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRE & _ & _ & _).
pose proof HK as (Hbl & _ & _ & _ & _ & _ & _ & _ & _ & V176 & _).
pose proof HDR as (R6 & R18 & R25 & R26).
pose proof HDM as (HZnm & HZdp & HBdp).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof (pa_base_lo (PL := PL_identb)) as HBLO.
destruct (jl1_geo LAWS HSTK g pos mf ly3 S3 W3 mem3 md3 _ HJ Hfrs Hmfb)
  as (EF & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
pose proof HJ as (HAR3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (Hin4 : In (4, pos) (frames S3)) by (rewrite Hfrs; left; reflexivity).
assert (Hti : 0 <= SlotModel.t_in (e_pl g) < 256) by exact (SlotModel.inb_range _ _).
pose proof (LLVMFuzzerTestOneInput_seg_J_model.m1_n_ln_le (e_pl g) Hwok) as HLn.
assert (HL1 : 1 <= j_L1 (e_pl g) <= 21) by exact HLn.
assert (HD1 : 1 <= put_dec_c.dec_len (SlotModel.t_in (e_pl g)) 1 <= 2)
  by exact (proj1 (LLVMFuzzerTestOneInput_seg_J_model.m2_d_range (e_pl g) Hwok)).
assert (Esh : shadow_addr (SFa g pos) = SHADOW_OFF + SFa g pos / 8) by reflexivity.
(* ---- run 1: 0x81f3c .. the call at 0x81f54 ---- *)
remember (Eimg (Ereg regs3 [Z_to_bv 64 (SlotModel.t_in (e_pl g))])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs3 r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 (SlotModel.t_in (e_pl g)))
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
assert (AGE : env_agree 32 (Ereg regs3 [Z_to_bv 64 (SlotModel.t_in (e_pl g))]) E)
  by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HS : st_ok_pi SEGS VAL E ss_jl1a
  (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + 0x17c8)) mem3 (seg_rom SEGS)))).
{ rewrite HE. apply (jl1_ent1 W3 regs3 mem3 mf _ Rs1); [clear - G5; lia | clear - G6 Hmfb; lia | exact Hti | exact V176 |].
  intros o Ho. apply Hpres. clear - Ho Hmfb G7. lia. }
clear HE.
assert (U9 : bv_unsigned (ew E 9) = mf)
  by (rewrite (EE 9%nat 9%bv eq_refl), Rs1; apply unsigned_lit_small; clear - G5 G6 Hmfb C1; lia).
unfold cfg_at. change (w64 (BASE + 0x17c8)) with (Z_to_bv 64 (BASE + 0x17c8)).
change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 (BASE + 0x17c8)) mem3 (seg_rom SEGS))) in HJ.
paj_run_shc RUNP RUNC HS HJ.
{ intros a (r & Hr & Ha). unfold ss_jl1a in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | []]. unfold jl1_r1 in Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  rewrite U9 in Ha. left. clear - Ha Hmfb G7. lia. }
rename ms into ms1. rename HJ into HJ1. rename HS into HS1.
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf + 200 <= a < mf + 208) ->
  aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha Hw.
  apply (kept_of_frame E _ (w_H W3) mem3 (ms_mem ms1) (fun x => mf + 200 <= x < mf + 208) HFr); [|exact Ha|exact Hw].
  intros bb wlo whi aa Hin Hr. unfold ss_jl1a, windows in Hin. cbn in Hin.
  destruct Hin as [Eq | []]. injection Eq as <- <- <-. cbn [base_val] in Hr. rewrite U9 in Hr. clear - Hr. lia. }
clear HF HFr HG.
assert (RK1 : forall r, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 21%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] ->
  getr (ms_regs ms1) r = getr regs3 r)
  by (eapply (regs_kept_of_st_ok SEGS E _ _ regs3 _ _ HS1 AGE); vm_compute; reflexivity).
prreg HS1 (1%bv : bv 5) Q1. prreg HS1 (10%bv : bv 5) Q10. prreg HS1 (11%bv : bv 5) Q11.
prreg HS1 (12%bv : bv 5) Q12. prreg HS1 (13%bv : bv 5) Q13.
rewrite (EE 26%nat 26%bv eq_refl), R26 in Q10. rewrite U9 in Q11. rewrite E32 in Q12.
assert (Q2 : getr (ms_regs ms1) 2 = w64 mf) by (rewrite (RK1 2%bv ltac:(jl1_in)); exact Rsp).
assert (Q3 : getr (ms_regs ms1) 3 = w64 (as_gp B)) by (rewrite (RK1 3%bv ltac:(jl1_in)); exact Rgp).
assert (Q4 : getr (ms_regs ms1) 4 = w64 (as_tp B)) by (rewrite (RK1 4%bv ltac:(jl1_in)); exact Rtp).
assert (Qsp : spZ (ms_regs ms1) = mf)
  by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; clear - G5 G6 Hmfb C1; lia).
(* the counter mf+200 holds ld + 2 *)
assert (V200 : val_mem SEGS (rd W3 (ms_mem ms1)) (mf + M_n2) 8 (j_L1 (e_pl g) + 2)).
{ unfold M_n2.
  lazymatch type of HS1 with st_ok _ _ ?ssx _ =>
    let rs := eval vm_compute in (ss_mem ssx) in
    lazymatch rs with
    | context [YP09.mkChunk 200 (CVal 8 ?e)] =>
      apply (jl1_chunk E ssx (restrict (w_H W3) ms1) 0 _ 200 8 e mf (j_L1 (e_pl g) + 2) HS1 eq_refl)
    end end.
  - cbn [base_val YP09.r_base]. exact U9.
  - cbn [YP09.r_chunks]. repeat (first [apply in_eq | apply in_cons]).
  - cbn [sv_denot]. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned.
    rewrite ?(EE 12%nat 12%bv eq_refl), ?(EE 11%nat 11%bv eq_refl), ?R12, ?R11. unfold w64.
    rewrite ?alu64_add_lit. f_equal. ring.
  - clear - HL1. lia.
  - lia. }
(* exp_dp's 64 bytes are addressable at the call: their shadow is zero (run 1 wrote only mf+200..207) *)
assert (HRA : range_addressable (aview SEGS (w_H W3) (ms_mem ms1)) SHADOW_OFF (SFa g pos + V_dp) N_dp).
{ apply (jl1_ra _ (SFa g pos + V_dp) N_dp); [| |unfold N_dp; reflexivity | lia | lia].
  - unfold sh_zero in HZdp. apply (j_zero_shadow_moved (aview SEGS (w_H W3) mem3)); [|exact HZdp].
    intros i Hi. apply KEEP1.
    + unfold shadow_of_addr, V_dp, N_dp in *. change (64 / 8) with 8 in Hi. clear - Hi G1 G2 G4 C1.
      unfold SHADOW_OFF. lia.
    + unfold shadow_of_addr, V_dp, N_dp in *. change (64 / 8) with 8 in Hi. clear - Hi G1 G2 G4 G5 C1.
      unfold SHADOW_OFF. lia.
  - unfold V_dp. clear - G4. lia. }
(* ---- the call put_dec(&exp_dp, mf+200, t_in, 1) at 0x81f54 ---- *)
pmkst HS1.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) ?Q =>
  change (SRr SEGS W3 (cfg_at SEGS (SIGMA IB_put_dec) rg mm mdx) Q) end.
eapply SRr_bind.
{ apply (jl1_pd LAWS PSIG HPD HSTK HEV g pos mf W3 (ms_regs ms1) (ms_mem ms1) _ ly3 S3 _ (j_L1 (e_pl g) + 2)
    (SlotModel.t_in (e_pl g)) 0x17e4 HPRE HJ1 Hfrs Hk Hmfb Hmf32 Q1 ltac:(lia) eq_refl Q2 Q3 Q4 Q10).
  - unfold M_n2. exact Q11.
  - exact Q12.
  - exact Q13.
  - exact Hti.
  - clear - HL1. lia.
  - unfold N_dp. clear - HL1 HD1. lia.
  - exact V200.
  - exact HRA. }
cbv beta. intros W4 c4 _ HPOST.
destruct HPOST as (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & HF4 & HB4 & HT4 & HG4 & HV4).
rewrite Q1.
replace (4 * Z.of_nat (m_nrec g) + 7 + put_dec.EV_PUT_DEC) with (4 * Z.of_nat (m_nrec g) + 7) in HJ4
  by (unfold put_dec.EV_PUT_DEC; ring).
rewrite Qsp in HT4. destruct HT4 as (T1 & T2 & _ & T4 & _).
clear HS1 HJ1.
(* what the call and run 1 kept *)
assert (KM4 : forall a, mf <= a < e_sp0 g -> ~ (mf + 200 <= a < mf + 208) ->
  aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha Hw. transitivity (aview SEGS (w_H W3) (ms_mem ms1) a).
  - apply T1.
    + clear - Ha G5 G6. lia.
    + unfold put_dec.PUT_DEC_STK, ESTACK. clear - Ha. lia.
    + intros [HE | HE].
      * unfold M_n2 in HE. clear - HE Hw. lia.
      * unfold V_dp in HE. clear - HE Ha G2 G5 HD1 HL1. lia.
  - apply KEEP1; [clear - Ha G5 G6 C1; lia | exact Hw]. }
assert (KF4 : forall a, SFa g pos <= a < SFa g pos + 1024 ->
  ~ (SFa g pos + V_dp + (j_L1 (e_pl g) + 2) <= a <
     SFa g pos + V_dp + (j_L1 (e_pl g) + 2) + put_dec_c.dec_len (SlotModel.t_in (e_pl g)) 1) ->
  aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha Hw. transitivity (aview SEGS (w_H W3) (ms_mem ms1) a).
  - apply (T4 4 pos a Hin4).
    + left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF. change (fs_frame_bytes 4) with 1024. clear - Ha. lia.
    + intros [HE | HE]; [unfold M_n2 in HE; clear - HE Ha G2 G5; lia | exact (Hw HE)].
  - apply KEEP1; [clear - Ha G1 G2 C1; lia | clear - Ha G2 G5; lia]. }
assert (KSH4 : forall a, shadow_addr (SFa g pos) <= a < shadow_addr (SFa g pos) + 128 ->
  aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. transitivity (aview SEGS (w_H W3) (ms_mem ms1) a).
  - apply (T4 4 pos a Hin4).
    + right. unfold in_zr. cbn [fst snd]. rewrite EF. change (fs_frame_bytes 4 / 8) with 128. exact Ha.
    + intros [HE | HE]; [unfold M_n2 in HE; clear - HE Ha G9 G5; lia | unfold V_dp in HE; clear - HE Ha G10 HD1 HL1; lia].
  - apply KEEP1; [clear - Ha G8 G9 C1; lia | clear - Ha G9 G5; lia]. }
assert (KB4 : forall b m i, In (b, m) (ablocks B ly3 S3) -> 0 <= i < req_size m ->
  aview SEGS (w_H W4) mem4 (b + i) = aview SEGS (w_H W3) mem3 (b + i)).
{ intros b m i Hin Hi.
  destruct (al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 b m HAR3 Hin) as (_ & Hb1 & Hb2 & _).
  pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 mem3 md3 b m 4 pos HAR3 Hin Hin4) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EF in Hd. change (fs_frame_bytes 4) with 1024 in Hd.
  transitivity (aview SEGS (w_H W3) (ms_mem ms1) (b + i)).
  - apply (T2 b m i Hin Hi). intros [HE | HE].
    + unfold M_n2 in HE. clear - HE Hi Hb2 G5. lia.
    + unfold V_dp in HE. clear - HE Hi Hd HD1 HL1. lia.
  - apply KEEP1; [clear - Hi Hb1 Hb2 C1; lia | clear - Hi Hb2 G5; lia]. }
(* ---- run 2: 0x81f58 (x6 = mf+168) .. 0x81f5c ---- *)
assert (R9_4 : getr regs4 9 = w64 mf)
  by (rewrite (jl1_pres _ _ HP4 9%bv ltac:(jl1_in)), (RK1 9%bv ltac:(jl1_in)); exact Rs1).
assert (V168_4 : val_mem SEGS (rd W4 mem4) (mf + 168) 8 SHADOW_OFF).
{ apply (val_mem_kept SEGS (w_H W3) (w_H W4) mem3 mem4 (mf + 168) 8 SHADOW_OFF); [|exact V168].
  intros kk Hkk. apply KM4; [clear - Hkk Hmfb; lia | clear - Hkk; lia]. }
remember (Eimg (Ereg regs4 [Z_to_bv 64 SHADOW_OFF])) as E2 eqn:HE2.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply Eimg_env).
assert (E2_32 : ew E2 32 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite HE2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs4 _ 0)).
assert (AGE2 : env_agree 32 (Ereg regs4 [Z_to_bv 64 SHADOW_OFF]) E2)
  by (rewrite HE2; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HS2 : st_ok_pi SEGS VAL E2 ss_jl1b
  (restrict (w_H W4) (mkst regs4 (Z_to_bv 64 (BASE + 0x17e4)) mem4 (seg_rom SEGS)))).
{ rewrite HE2. apply (jl1_ent2 W4 regs4 mem4 mf R9_4); [clear - G5; lia | clear - G6 Hmfb; lia | exact V168_4]. }
clear HE2.
change mem4 with (ms_mem (mkst regs4 (Z_to_bv 64 (BASE + 0x17e4)) mem4 (seg_rom SEGS))) in HJ4.
paj_run_to_sh RUNTOP HS2 HJ4 0x17e8.
{ cbn [ss_mem ss_jl1b]. apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo jl1_r2]; lia | apply awr_ok_nil]. }
cbn [ms_mem mkst] in HF, HFr, HG, HJ4.
assert (EQR2 : mrestrict (w_H W4) (ms_mem ms) = mrestrict (w_H W4) mem4).
{ apply (frame_of_read_only E2 (ss_mem ss_jl1b)); [reflexivity | exact HFr]. }
assert (EQV2 : aview SEGS (w_H W4) (ms_mem ms) = aview SEGS (w_H W4) mem4)
  by (unfold aview; rewrite EQR2; reflexivity).
assert (RK2 : forall r, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 21%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] ->
  getr (ms_regs ms) r = getr regs4 r)
  by (eapply (regs_kept_of_st_ok_pi E2 _ _ regs4 _ _ HS2 AGE2); vm_compute; reflexivity).
assert (RR : forall r, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 21%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] ->
  getr (ms_regs ms) r = getr regs3 r).
{ intros r Hr. rewrite (RK2 r Hr), (jl1_pres _ _ HP4 r Hr). exact (RK1 r Hr). }
prreg HS2 (6%bv : bv 5) Q6. rewrite E2_32 in Q6.
assert (HBL4 : hblocks B g ly4 S4 [(nm, Z.max (SlotModel.t_cap_name (e_pl g)) 1);
  (tk, Z.max (SlotModel.t_cap_tok (e_pl g)) 1); (dp, Z.max (SlotModel.t_cap_disp (e_pl g)) 1)])
  by (unfold hblocks in *; rewrite HB4; exact Hbl).
(* ---- the boundary jc7 at 0x81f5c ---- *)
apply SRr_ret. unfold jc7, acut. pmkst HS2.
lazymatch type of HJ4 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ =>
  exists ly4, S4, (ms_regs ms), (ms_mem ms), mdx end.
split; [reflexivity|]. split; [exact HJ4|]. split; [rewrite HF4; exact Hfrs|]. split; [exact Hk|].
split.
{ eapply (mo_le_mono MT MTL); [exact (mo_le_trans MT MTL _ _ _ _ _ MLE (HMT0 S3 S4))|].
  rewrite Z.add_0_r. apply Z.le_refl. }
split.
{ apply (mo_ok_step MT MTL S3 S4 0); [rewrite Z.add_0_l; exact MOK | exact (HMT0 S3 S4)]. }
split.
{ apply (jl1_ec_keep g pos mf ly3 S3 W3 regs3 mem3 md3 ly4 S4 W4 (ms_regs ms) (ms_mem ms) _ _ _ HC HJ4 HBL4).
  - exact (RR 2%bv ltac:(jl1_in)).
  - exact (RR 9%bv ltac:(jl1_in)).
  - exact (RR 8%bv ltac:(jl1_in)).
  - exact (RR 3%bv ltac:(jl1_in)).
  - exact (RR 4%bv ltac:(jl1_in)).
  - intros a Ha. rewrite EQV2. destruct Ha as [Ha | [Ha | Ha]].
    + apply KM4; [clear - Ha Hmfb; lia | clear - Ha; lia].
    + apply KM4; [clear - Ha Hmfb; lia | clear - Ha; lia].
    + apply KF4; [clear - Ha; lia | unfold V_dp; clear - Ha HL1 HD1; lia]. }
split.
{ apply (jl1_jkeep_keep g pos mf nm tk dp ly3 S3 W3 regs3 mem3 ly4 S4 W4 (ms_regs ms) (ms_mem ms) HK HB4
    (RR 21%bv ltac:(jl1_in)) (RR 23%bv ltac:(jl1_in)) (RR 24%bv ltac:(jl1_in)) G4 ltac:(clear - G1; lia)).
  - intros a Ha. rewrite EQV2. apply KM4; [clear - Ha Hmfb; lia | clear - Ha; lia].
  - intros a Ha. rewrite EQV2. apply KF4; [unfold V_id, N_id in Ha; clear - Ha; lia | unfold V_id, N_id, V_dp in *; clear - Ha HL1; lia].
  - intros a Ha. rewrite EQV2. exact (KSH4 a Ha).
  - intros b m i Hin Hi. rewrite EQV2. exact (KB4 b m i Hin Hi). }
split.
{ unfold jdp_regs. split; [exact Q6|].
  split; [rewrite (RR 18%bv ltac:(jl1_in)); exact R18|].
  split; [rewrite (RR 25%bv ltac:(jl1_in)); exact R25|].
  rewrite (RR 26%bv ltac:(jl1_in)); exact R26. }
split.
{ unfold jdp_mem. split; [|split].
  - unfold sh_zero in *. apply (j_zero_shadow_moved (aview SEGS (w_H W3) mem3)); [|exact HZnm].
    intros i Hi. rewrite EQV2. apply KSH4. unfold shadow_of_addr, V_nm, N_nm in *. rewrite Esh.
    change (32 / 8) with 4 in Hi. clear - Hi G4. lia.
  - unfold sh_zero in *. apply (j_zero_shadow_moved (aview SEGS (w_H W3) mem3)); [|exact HZdp].
    intros i Hi. rewrite EQV2. apply KSH4. unfold shadow_of_addr, V_dp, N_dp in *. rewrite Esh.
    change (64 / 8) with 8 in Hi. clear - Hi G4. lia.
  - rewrite jl1_dp2. unfold bytes_at8 in *. rewrite map_app. apply (proj2 (garr8_app SEGS _ _ _ _)). split.
    + apply (garr8_frame SEGS _ _ _ _ HBdp). intros a Ha. apply (mbyte_of_aview SEGS). rewrite EQV2.
      rewrite length_map, length_app, Nat2Z.inj_add, jl1_lit_len in Ha.
      change (Z.of_nat (length (j_dp1 (e_pl g)))) with (j_L1 (e_pl g)) in Ha. change (Z.of_nat 2) with 2 in Ha.
      apply KF4; [unfold V_dp in Ha; clear - Ha HL1; lia | unfold V_dp in *; clear - Ha; lia].
    + replace (SFa g pos + V_dp + Z.of_nat (length (map (fun b : byte => bv_unsigned b) (j_dp1 (e_pl g) ++ j_lit_paren))))
        with (SFa g pos + V_dp + (j_L1 (e_pl g) + 2))
        by (rewrite length_map, length_app, Nat2Z.inj_add, jl1_lit_len; reflexivity).
      rewrite EQR2. exact HG4. }
split; [rewrite (RR 27%bv ltac:(jl1_in)); exact R27|].
split; [rewrite EQR2; exact HV4|].
unfold bytes_at8 in *. apply (garr8_frame SEGS _ _ _ _ HNM). intros a Ha. apply (mbyte_of_aview SEGS). rewrite EQV2.
rewrite length_map, length_app, Nat2Z.inj_add in Ha. cbn [length] in Ha.
change (Z.of_nat (length (SlotModel.n_EXP_NM (e_pl g)))) with (SlotModel.n_ln (e_pl g)) in Ha.
change (Z.of_nat 1) with 1 in Ha.
apply KF4; [unfold V_nm in Ha; clear - Ha HLn; lia | unfold V_nm, V_dp in *; clear - Ha HLn HL1; lia].
Qed.

(* ---- the piece ------------------------------------------------------------------------------------------------ *)
Lemma j_lit1_glue : j_lit1_glue_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS G.
Proof using RO HRO HIMG AJ_NIL_IO.
unfold j_lit1_glue_stmt.
intros LAWS HSTK HEV HPD PSIG MTL HMT0 HGM HG9 HLIT g pos mf nm tk dp W2 c2 Hc6 Hwok.
eapply SRr_bind; [exact (jl1_head g pos mf nm tk dp W2 c2 LAWS HGM HG9 Hc6 Hwok)|].
intros W3 c3 _ H3.
eapply SRr_bind; [exact (HLIT LAWS g pos mf nm tk dp 0 W3 c3 H3)|].
intros W4 c4 _ H4.
exact (jl1_tail g pos mf nm tk dp W4 c4 LAWS HSTK HEV HPD PSIG MTL HMT0 H4 Hwok).
Qed.

End c.
End b.
End a.
