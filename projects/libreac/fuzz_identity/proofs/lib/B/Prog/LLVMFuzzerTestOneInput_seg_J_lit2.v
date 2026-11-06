(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:1527-1530,
   1556-1561, for libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_D4.v, with its module names and addresses changed; 576 of its 647 lines of code are new or changed and 867 lines of the source are left out. *)
(* j_lit2 of lib/B/Prog/LLVMFuzzerTestOneInput_seg_J_loops_stmt.v: the copy of the literal " in / " (object 10)
   into `exp_dp` (SF+592) at offset ld = n_ln + 2 + |DEC t_in 1|, the loop 0x81f78 .. 0x81fb8 of
   LLVMFuzzerTestOneInput's build-B walk (fuzz_identity.asan-ubsan), from the loop head BASE + 0x1804 to the
   exit slot BASE + 0x186c.

   The count is the literal 6, so one run of the token engine (IdentBPaLib.paj_run_to_tok) covers the rest of
   the loop from any entry index i = 0 .. 5, from a fresh symbolic state j2_ss i:
     - a1 (index), a5 (count), a6 (the byte to store) and t1 (the shadow base) are pinned to literals, a3 to
       the literal's image atom;
     - the store `exp_dp[ld + i] = a6` writes region j2_rD, based at a4 = &exp_dp + ld with the window [i, 6);
       its shadow test goes through the token engine's shadow entry j2_SH ([a4, a4 + 14) is addressable: the
       shadow of `exp_dp` is cleared, jdp_mem; 14 >= 5 + 8, so every test finds its 8 bytes covered and the
       engine reads the shadow byte as 0 without a token), which also covers the region's window (cells_safe);
     - the look-ahead test of `lit + i + 1` compares the shadow byte with the loop index + 1 (slli / srai),
       not with `andi addr, 7`, so the token engine's slow-block pattern (YCbn.slow_block) does not apply: the
       state holds the literal's shadow byte as region j2_rS (based at the extra atom 32 = lit / 8, with the
       alias of (lit + j) >> 3, j = 1 .. 6), and the byte is the literal 7 (block_shadow lit 7 of the premise:
       lit mod 8 = 0 and one granule holding 7), so the test passes for i + 1 < 7; the literal's seven bytes
       are region j2_rL (bytes_at8 of the premise);
     - the UBSan bound `bltu ~&exp_dp, ld + i` is decided by the ranges of atoms 18 and 12.
   The technique is the one of lib/B/Prog/reac_box_name_seg_lit.v:
   the literal's shadow byte in the symbolic state, its bytes from the premise. The proof's shape
   is j_lit1's (lib/B/Prog/LLVMFuzzerTestOneInput_seg_J_lit1.v): the run stores only into
   [a4 + i, a4 + 6), inside the class-4 frame (4, pos), so every other fact of the cut is carried (j2_exit). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentBase IdentRo YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_seg_J_loops_stmt.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require LLVMFuzzerTestOneInput_seg_J_model.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec.
Import ListNotations.
(* reac_box_name_seg_*.v set lia's euclidean-division flag to false for every file that loads reac_box_name
   (through the contract); this file was proved with it on, so it turns it back on. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the literal, as a list of bytes ---------------------------------------------------------------------- *)
Definition j2_lit : list Z := [32; 105; 110; 32; 47; 32].
Lemma j2_len_lit : length j_lit_in = 6%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma j2_map_lit : map (fun b : byte => bv_unsigned b) j_lit_in = j2_lit.
Proof. vm_compute. reflexivity. Qed.
Lemma j2_map_lit0 : map (fun b : byte => bv_unsigned b) (j_lit_in ++ [RcIdentModel.zb 0]) = [32; 105; 110; 32; 47; 32; 0].
Proof. vm_compute. reflexivity. Qed.
Lemma j2_nth_firstn : forall (A : Type) (d : A) m k (l : list A), (k < m)%nat -> nth k (firstn m l) d = nth k l d.
Proof.
intros A d m. induction m as [|m IH]; intros k l Hk; [exfalso; lia|].
destruct l as [|x l]; cbn [firstn]; [destruct k; reflexivity|].
destruct k as [|k]; cbn [nth]; [reflexivity | apply IH; lia].
Qed.
(* The j-th byte of a prefix of the literal, as a Z. *)
Lemma j2_nth_pref : forall m j, (j < m)%nat -> (m <= 6)%nat ->
  nth j (map (fun b : byte => bv_unsigned b) (firstn m j_lit_in)) 0 = nth j j2_lit 0.
Proof.
intros m j Hj Hm.
rewrite <- j2_map_lit.
rewrite (nth_indep (map (fun b : byte => bv_unsigned b) (firstn m j_lit_in)) 0
  (bv_unsigned (RcIdentModel.zb 0))) by (rewrite length_map, length_firstn, j2_len_lit; lia).
rewrite (nth_indep (map (fun b : byte => bv_unsigned b) j_lit_in) 0 (bv_unsigned (RcIdentModel.zb 0)))
  by (rewrite length_map, j2_len_lit; lia).
rewrite !map_nth. f_equal. apply j2_nth_firstn. exact Hj.
Qed.

(* ---- the symbolic state at the loop head, BASE + 0x1804 --------------------------------------------------- *)
(* a4 (atom 14) = &exp_dp + ld: the bytes [a4 + i, a4 + 6) the run stores. *)
Definition j2_rD (i : Z) : YP09.region := YP09.mkRegion (Some 14%nat) i 6 i 6 [].
(* The literal " in / " with its NUL, at its image atom. *)
Definition j2_rL : YP09.region := YP09.mkRegion (Some (A_OBJ 10)) 0 7 0 0
  [YP09.mkChunk 0 (CVal 1 (SLit 32)); YP09.mkChunk 1 (CVal 1 (SLit 105)); YP09.mkChunk 2 (CVal 1 (SLit 110));
   YP09.mkChunk 3 (CVal 1 (SLit 32)); YP09.mkChunk 4 (CVal 1 (SLit 47)); YP09.mkChunk 5 (CVal 1 (SLit 32));
   YP09.mkChunk 6 (CVal 1 (SLit 0))].
(* The literal's shadow byte, at SB + lit / 8 (atom 32 = lit / 8). *)
Definition j2_rS : YP09.region := YP09.mkRegion (Some 32%nat) SB (SB + 1) 0 0 [YP09.mkChunk SB (CVal 1 (SLit 7))].
Definition j2_ch (i : Z) : Z := nth (Z.to_nat i) j2_lit 0.
Definition j2_pin (i : Z) : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 6%bv (SLit SB)) 11%bv (SLit i)) 13%bv (SOff (A_OBJ 10) 0))
    15%bv (SLit 6)) 16%bv (SLit (j2_ch i)).
(* x12 = ld in [4, 25] (n_ln_le, m2_d_range), a4 inside the frame, x18 = ~&exp_dp;
   (lit + j) >> 3 = lit / 8 for j = 1 .. 6. *)
Definition j2_G : facts :=
  mkFacts [(12%nat, mkAF 4 25 0); (14%nat, mkAF 4096 0x7fffff800000 0);
           (18%nat, mkAF (2 ^ 64 - 2 ^ 47) (2 ^ 64 - 4097) 0)] []
    [(SAlu ALU_SRL (SOff (A_OBJ 10) 1) (SLit 3), SOff 32 0);
     (SAlu ALU_SRL (SOff (A_OBJ 10) 2) (SLit 3), SOff 32 0);
     (SAlu ALU_SRL (SOff (A_OBJ 10) 3) (SLit 3), SOff 32 0);
     (SAlu ALU_SRL (SOff (A_OBJ 10) 4) (SLit 3), SOff 32 0);
     (SAlu ALU_SRL (SOff (A_OBJ 10) 5) (SLit 3), SOff 32 0);
     (SAlu ALU_SRL (SOff (A_OBJ 10) 6) (SLit 3), SOff 32 0)].
Definition j2_ss (i : Z) : sstate := mkSS 0x1804 (j2_pin i) [j2_rD i; j2_rL; j2_rS] None j2_G.
Definition j2_Bx : sv := SLit SB.
Definition j2_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition j2_SH : list shent := [mkSHE 14 0 14].
(* The registers the run keeps that the exit cut states. *)
Definition j2_KL : list (bv 5) :=
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 12%bv; 18%bv; 21%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv].

(* ---- the model: |n_TK| = n_lt (twin of lib/Prog/Seg/Tac_sh1.v tok_go_len / n_TK_len, whose import closure,
   the plain slot walk's lib/Lib, the B walk does not build) ---------------------------------------------------- *)
Lemma j2_tok_go_len : forall l d, length (SlotModel.tok_go d l) =
  (length l - (if negb d && SlotModel.has_dash l then 1 else 0))%nat.
Proof.
induction l as [|b r IH]; intros d.
- destruct d; reflexivity.
- cbn [SlotModel.tok_go].
  change (SlotModel.has_dash (b :: r)) with ((RcIdentModel.bz b =? 45) || SlotModel.has_dash r).
  destruct d; cbn [negb andb].
  + cbn [length]. rewrite IH. cbn [negb andb]. lia.
  + destruct (Z.eqb_spec (RcIdentModel.bz b) 45) as [E|E]; cbn [orb].
    * rewrite IH. cbn [negb andb length]. lia.
    * cbn [length]. rewrite IH. cbn [negb andb]. destruct (SlotModel.has_dash r) eqn:Hr; [|lia].
      assert (length r >= 1)%nat by (destruct r; [discriminate|cbn; lia]). lia.
Qed.
Lemma j2_n_TK_len : forall inp, Z.of_nat (length (SlotModel.n_TK inp)) = SlotModel.n_lt inp.
Proof.
intros inp. unfold SlotModel.n_TK, SlotModel.TOK, SlotModel.n_lt, SlotModel.n_ln. rewrite j2_tok_go_len.
cbn [negb andb].
destruct (SlotModel.has_dash (SlotModel.n_EXP_NM inp)) eqn:H; [|lia].
destruct (SlotModel.n_EXP_NM inp) as [|x r]; [discriminate|]. cbn [length]. lia.
Qed.
(* The length of the display before this literal, and its range. *)
Lemma j2_len_dp2 : forall inp, Z.of_nat (length (j_dp2 inp)) = j_L2 inp.
Proof. intro inp. exact (LLVMFuzzerTestOneInput_seg_J_model.m2_len2 inp). Qed.
Lemma j2_L2_range : forall inp, SlotModel.n_wok inp = true -> 4 <= j_L2 inp <= 25.
Proof.
intros inp Hw. pose proof (SlotModel.n_ln_le inp Hw) as H1.
destruct (LLVMFuzzerTestOneInput_seg_J_model.m2_d_range inp Hw) as [Hd1 _].
unfold j_L2, j_L1, j_d1. unfold LLVMFuzzerTestOneInput_seg_J_model.m2_d1 in Hd1. lia.
Qed.

(* ---- arithmetic ---- *)
Lemma j2_mod8 : forall x c, x mod 32 = 0 -> c mod 8 = 0 -> (x + c) mod 8 = 0.
Proof.
intros x c Hx Hc. pose proof (Z.div_mod x 32 ltac:(lia)) as Dx. pose proof (Z.div_mod c 8 ltac:(lia)) as Dc.
rewrite Hx, Z.add_0_r in Dx. rewrite Hc, Z.add_0_r in Dc.
replace (x + c) with ((4 * (x / 32) + c / 8) * 8) by lia. apply Z.mod_mul. lia.
Qed.
Lemma j2_lnot64 : forall x, 0 <= x < 2 ^ 64 -> bv_unsigned (w64 (Z.lnot x)) = 2 ^ 64 - 1 - x.
Proof.
intros x Hx. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
assert (Hn : Z.lnot x = (2 ^ 64 - 1 - x) + (-1) * 2 ^ 64) by (rewrite Z.lnot_eq_pred_opp; lia).
rewrite Hn, Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
(* (x + j) >> 3 = x / 8 for x 8-aligned and j < 8: the alias of j2_G. *)
Lemma j2_alias : forall E (n : nat) (x j : Z), bv_unsigned (ew E n) = x -> bv_unsigned (ew E 32) = x / 8 ->
  x mod 8 = 0 -> 0 <= x -> x + 8 <= 2 ^ 64 -> 0 <= j < 8 ->
  sv_denot E (SAlu ALU_SRL (SOff n j) (SLit 3)) = sv_denot E (SOff 32 0).
Proof.
intros E n x j Hx H32 Hal Hx0 Hx8 Hj. apply U_inj. rewrite U_SAlu, !U_SOff.
assert (U3 : U E (SLit 3) = 3) by (rewrite U_SLit; reflexivity).
rewrite U3, Hx, H32. cbn [zalu_raw]. change (Z.land 3 63) with 3. unfold zcanon, M64.
rewrite (Z.mod_small (x + j)) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite Z.add_0_r. f_equal.
rewrite (Z.div_mod x 8) at 1 by lia. rewrite Hal, Z.add_0_r.
replace (8 * (x / 8) + j) with (j + x / 8 * 8) by lia.
rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

(* The environment of the run: the registers, and atom 32 = lit / 8. *)
Definition j2_E (regs : bvmap 5 word) : env := Eimg (Ereg regs [Z_to_bv 64 (VAL (A_OBJ 10) / 8)]).

Lemma j2_val_mem1 : forall H m a v, aview SEGS H m a = Some v -> val_mem SEGS (mrestrict H m) a 1 v /\ 0 <= v < 256.
Proof.
intros H m a v E. unfold aview in E.
destruct (mbyte SEGS (mrestrict H m) a) as [b|] eqn:Hb; cbn [option_map] in E; [|discriminate].
injection E as <-. pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
split; [|lia]. intros k Hk. assert (k = 0%nat) by lia. subst k. rewrite Z.add_0_r, Hb. f_equal.
apply bv_eq. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte.
change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256. unfold bv_wrap. change (bv_modulus 8) with 256.
rewrite !(Z.mod_small (bv_unsigned b) 256) by lia. reflexivity.
Qed.

(* What the run kept: every byte outside the window [a4 + i, a4 + 6) of j2_rD. *)
Lemma j2_K : forall E (i D : Z) (H : word -> bool) (m m' : word -> option byte),
  bv_unsigned (ew E 14) = D -> frame_of E (ss_mem (j2_ss i)) (mrestrict H m) (mrestrict H m') ->
  forall a, 0 <= a < 2 ^ 64 -> a < D + i \/ D + 6 <= a -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E i D H m m' U14 HFr a Ha Hout. apply (aview_eq_of SEGS). apply HFr.
rewrite unsigned_lit_small by exact Ha.
intros (r & Hin & Hr). unfold j2_ss in Hin. cbn [ss_mem In] in Hin.
destruct Hin as [<- | [<- | [<- | []]]];
  cbn [j2_rD j2_rL j2_rS YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; [rewrite U14 in Hr|..]; lia.
Qed.

(* A byte of region 0 (base atom 14) of a state the engine reached. *)
Lemma j2_chunk : forall E ss ms r off (v D : Z),
  st_ok_pi SEGS VAL E ss ms -> nth_error (ss_mem ss) 0 = Some r -> YP09.r_base r = Some 14%nat ->
  bv_unsigned (ew E 14) = D ->
  In (YP09.mkChunk off (CVal 1 (SLit v))) (YP09.r_chunks r) -> 0 <= v < 256 ->
  val_mem SEGS (ms_mem ms) (D + off) 1 v.
Proof.
intros E ss ms r off v D HS Hn Hb U14 Hin Hv.
pose proof (st_ok_pi_region_nth E ss ms 0 r HS Hn) as (_ & _ & _ & Hc).
rewrite Hb in Hc. cbn [base_val] in Hc. rewrite U14 in Hc.
exact (val_of_chunk_ok SEGS E (ms_mem ms) D off 1 (SLit v) v (proj1 (Forall_forall _ _) Hc _ Hin) eq_refl
  ltac:(cbn; lia) ltac:(lia)).
Qed.
Section c.
(* The Section variables j_lit2_stmt takes (the Section of the statement file without XN_LIB, which the
   statement does not use), in the same order. *)
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.

#[local] Notation ACUT := (acut B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation ECOMMON := (ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation AJ g pos := (ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
[(4, pos)]).

(* ---- where things lie at a cut of the segment ---- *)
Lemma j2_geo : forall (LAWS : AR_laws SEGS B) g pos mf ly2 S2 W2 mem2 md2 k,
  AJ g pos ly2 S2 W2 mem2 md2 k -> frames S2 = [(4, pos)] -> e_sp0 g - 336 <= mf <= e_sp0 g - 320 ->
  AR SEGS B ly2 S2 W2 mem2 md2 /\ In (4, pos) (frames S2) /\ frame_addr ly2 4 pos = SFa g pos /\
  4096 <= SFa g pos /\ SFa g pos + 1024 <= alloc_ceiling /\ in_app (SFa g pos) 1024 /\ SFa g pos mod 32 = 0 /\
  alloc_ceiling <= e_sp0 g /\ e_sp0 g <= 2 ^ 47.
Proof.
intros LAWS g pos mf ly2 S2 W2 mem2 md2 k HJ HFR Hmf.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
assert (Efa : frame_addr ly2 4 pos = SFa g pos).
{ unfold SFa, frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite HFR; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 4 pos HAR Hin4) as (F1 & F2 & F3).
destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 4 pos HAR Hin4) as (F32 & _).
change (fs_frame_bytes 4) with 1024 in F2, F3.
rewrite Efa in F1, F2, F3, F32.
split; [exact HAR|]. split; [exact Hin4|]. split; [exact Efa|].
split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F32|].
clear - Hstk0 Hceil Hslo Hshi H47. split; lia.
Qed.
(* ---- the entry state of the run ---- *)
Lemma j2_entry : forall (LAWS : AR_laws SEGS B) g pos mf nm tk dp (i : Z) ly2 S2 W2 regs2 mem2 md2 k,
  AJ g pos ly2 S2 W2 mem2 md2 k -> frames S2 = [(4, pos)] -> e_sp0 g - 336 <= mf <= e_sp0 g - 320 ->
  j_lit_pre B g pos mf nm tk dp (VAL (A_OBJ 10)) j_lit_in
    (j_dp2 (e_pl g) ++ firstn (Z.to_nat i) j_lit_in) ly2 S2 W2 regs2 mem2 ->
  0 <= i < 6 -> (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5) ->
  getr regs2 11 = w64 i -> getr regs2 12 = w64 (j_L2 (e_pl g)) ->
  getr regs2 13 = w64 (VAL (A_OBJ 10)) ->
  getr regs2 14 = w64 (SFa g pos + V_dp + j_L2 (e_pl g)) -> getr regs2 15 = w64 6 ->
  getr regs2 16 = w64 (bv_unsigned (nth (Z.to_nat i) j_lit_in (RcIdentModel.zb 0))) ->
  st_ok_pi SEGS VAL (j2_E regs2) (j2_ss i)
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x1804)) mem2 (seg_rom SEGS))) /\
  sh_ok SEGS j2_Bx j2_SH (j2_E regs2) (mrestrict (w_H W2) mem2) /\
  awr_ok (j2_E regs2) (ss_mem (j2_ss i)) LLVMF_STK (e_sp0 g) [] (ablocks B (e_ly g) (e_S g)) (ablocks B ly2 S2)
    ly2 [(4, pos)] /\
  bv_unsigned (ew (j2_E regs2) 14) = SFa g pos + V_dp + j_L2 (e_pl g).
Proof.
intros LAWS g pos mf nm tk dp i ly2 S2 W2 regs2 mem2 md2 k HJ HFR Hmf Hpre Hi Hi6 R11 R12 R13 R14 R15 R16.
destruct (j2_geo LAWS g pos mf ly2 S2 W2 mem2 md2 k HJ HFR Hmf)
  as (HAR & Hin4 & Efa & HF0 & HF1 & HFapp & HF32 & Hceil & H47).
destruct Hpre as (_ & Hdpr & Hdpm & _ & _ & Hwok & _ & Hlb & Hlsh & Hlo & Hhi & _).
destruct Hdpr as (R6 & R18 & _ & _).
destruct Hdpm as (_ & Zd & _).
pose proof asan_consts as (C1 & _).
pose proof (j2_L2_range _ Hwok) as HL2.
set (SF := SFa g pos) in *. set (L2 := j_L2 (e_pl g)) in *.
pose proof (pa_val_range (A_OBJ 10)) as VO.
rewrite j2_len_lit in Hlsh, Hhi. change (Z.of_nat 6 + 1) with 7 in Hlsh. change (Z.of_nat 6) with 6 in Hhi.
destruct Hlsh as (Hal & _ & Hsh). specialize (Hsh 0 ltac:(clear; cbn; lia)).
change (if 0 <? 7 / 8 then 0 else 7 mod 8) with 7 in Hsh. rewrite Z.add_0_r in Hsh. unfold shadow_of_addr in Hsh.
unfold bytes_at8 in Hlb.
rewrite j2_map_lit0 in Hlb.
assert (ER : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (j2_E regs2) n = getr regs2 r)
  by (intros n r Hn; unfold j2_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U14 : bv_unsigned (ew (j2_E regs2) 14) = SF + V_dp + L2).
{ rewrite (ER 14%nat 14%bv eq_refl), R14. unfold w64. apply unsigned_lit_small. unfold V_dp.
  clear - HF0 HF1 HL2 C1. lia. }
assert (U12 : bv_unsigned (ew (j2_E regs2) 12) = L2).
{ rewrite (ER 12%nat 12%bv eq_refl), R12. unfold w64. apply unsigned_lit_small. clear - HL2. lia. }
assert (U18 : bv_unsigned (ew (j2_E regs2) 18) = 2 ^ 64 - 1 - (SF + V_dp)).
{ rewrite (ER 18%nat 18%bv eq_refl), R18. apply j2_lnot64. unfold V_dp. clear - HF0 HF1 C1. lia. }
assert (UO : bv_unsigned (ew (j2_E regs2) (A_OBJ 10)) = VAL (A_OBJ 10)).
{ unfold j2_E. rewrite Eimg_img by (clear; unfold A_OBJ, A_TEXT, A_LIM; lia). apply unsigned_lit_small. exact VO. }
assert (E32 : ew (j2_E regs2) 32 = Z_to_bv 64 (VAL (A_OBJ 10) / 8)).
{ unfold j2_E. rewrite Eimg_low by (clear; unfold A_TEXT; lia). exact (ew_Ereg_extra regs2 _ 0). }
assert (HO8 : 0 <= VAL (A_OBJ 10) / 8 <= VAL (A_OBJ 10)).
{ split; [apply Z.div_pos; clear - VO; lia | apply Z.div_le_upper_bound; clear - VO; lia]. }
assert (U32 : bv_unsigned (ew (j2_E regs2) 32) = VAL (A_OBJ 10) / 8).
{ rewrite E32. apply unsigned_lit_small. clear - VO HO8; lia. }
split.
{ (* the state *)
  rewrite restrict_mkst_fx. unfold j2_ss. apply pa_entry_st_ok_full.
  - unfold j2_pin.
    apply regs_ok_pin; [|discriminate|].
    + apply regs_ok_pin; [|discriminate|].
      * apply regs_ok_pin; [|discriminate|].
        -- apply regs_ok_pin; [|discriminate|].
           ++ apply regs_ok_pin; [|discriminate|].
              ** unfold j2_E. apply regs_ok_Eimg_Ereg.
              ** cbn [sv_denot]. exact R6.
           ++ cbn [sv_denot]. exact R11.
        -- cbn [sv_denot]. rewrite UO, Z.add_0_r. exact R13.
      * cbn [sv_denot]. exact R15.
    + cbn [sv_denot]. rewrite R16. unfold w64. f_equal. clear - Hi6.
      destruct Hi6 as [-> | [-> | [-> | [-> | [-> | -> ] ] ] ] ]; vm_compute; reflexivity.
  - clear - Hi6. destruct Hi6 as [-> | [-> | [-> | [-> | [-> | -> ] ] ] ] ]; vm_compute; reflexivity.
  - constructor; [|constructor; [|constructor; [|constructor]]].
    + unfold region_ok, j2_rD.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U14.
      split; [unfold V_dp; clear - HF0 HL2 Hi; lia|].
      split; [unfold V_dp; clear - HF1 HL2 C1; lia|].
      split; [|constructor].
      intros o' Ho'. apply (apresent_writable SEGS).
      destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 4 pos HAR Hin4) as (_ & _ & Hfb & _).
      rewrite Efa in Hfb. change (fs_frame_bytes 4) with 1024 in Hfb.
      apply (proj1 (Hfb (SF + V_dp + L2 + o') ltac:(unfold V_dp; clear - Ho' HL2 Hi; lia))).
    + unfold region_ok, j2_rL.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite UO.
      split; [clear - VO; lia|]. split; [clear - VO Hhi; lia|]. split; [intros o' Ho'; clear - Ho'; lia|].
      constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor;
        [|constructor]]]]]]].
      * apply (chunk_ok_val SEGS (j2_E regs2) _ (VAL (A_OBJ 10)) 0 1 (SLit 32) 32);
          [reflexivity | clear; cbn; lia | clear; lia | exact (proj1 (Hlb 0%nat ltac:(clear; cbn; lia)))].
      * apply (chunk_ok_val SEGS (j2_E regs2) _ (VAL (A_OBJ 10)) 1 1 (SLit 105) 105);
          [reflexivity | clear; cbn; lia | clear; lia | exact (proj1 (Hlb 1%nat ltac:(clear; cbn; lia)))].
      * apply (chunk_ok_val SEGS (j2_E regs2) _ (VAL (A_OBJ 10)) 2 1 (SLit 110) 110);
          [reflexivity | clear; cbn; lia | clear; lia | exact (proj1 (Hlb 2%nat ltac:(clear; cbn; lia)))].
      * apply (chunk_ok_val SEGS (j2_E regs2) _ (VAL (A_OBJ 10)) 3 1 (SLit 32) 32);
          [reflexivity | clear; cbn; lia | clear; lia | exact (proj1 (Hlb 3%nat ltac:(clear; cbn; lia)))].
      * apply (chunk_ok_val SEGS (j2_E regs2) _ (VAL (A_OBJ 10)) 4 1 (SLit 47) 47);
          [reflexivity | clear; cbn; lia | clear; lia | exact (proj1 (Hlb 4%nat ltac:(clear; cbn; lia)))].
      * apply (chunk_ok_val SEGS (j2_E regs2) _ (VAL (A_OBJ 10)) 5 1 (SLit 32) 32);
          [reflexivity | clear; cbn; lia | clear; lia | exact (proj1 (Hlb 5%nat ltac:(clear; cbn; lia)))].
      * apply (chunk_ok_val SEGS (j2_E regs2) _ (VAL (A_OBJ 10)) 6 1 (SLit 0) 0);
          [reflexivity | clear; cbn; lia | clear; lia | exact (proj1 (Hlb 6%nat ltac:(clear; cbn; lia)))].
    + unfold region_ok, j2_rS.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U32.
      split; [unfold SB; clear - HO8; lia|]. split; [unfold SB; clear - HO8 Hhi; lia|].
      split; [intros o' Ho'; clear - Ho'; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS (j2_E regs2) _ (VAL (A_OBJ 10) / 8) SB 1 (SLit 7) 7);
        [reflexivity | clear; cbn; lia | clear; lia |].
      replace (VAL (A_OBJ 10) / 8 + SB) with (SHADOW_OFF + VAL (A_OBJ 10) / 8) by (clear; unfold SB, SHADOW_OFF; lia).
      exact (proj1 (j2_val_mem1 _ _ _ _ Hsh)).
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val j2_rD j2_rL j2_rS]. rewrite U14, UO, U32.
    pose proof (frm_off_imgP B ly2 S2 W2 mem2 md2 4 pos HAR Hin4) as Hfi.
    rewrite Efa in Hfi. change (fs_frame_bytes 4) with 1024 in Hfi.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. unfold SB, V_dp.
    clear - Hfi HFapp HL2 Hi Hlo Hhi HO8 HF0 C1.
    repeat split; lia.
  - unfold facts_ok, j2_G. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; [exact I|]].
    + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U12, U14, U18. rewrite Z.pow_0_r, !Z.mod_1_r.
      unfold V_dp. clear - HL2 HF0 HF1 C1. repeat split; lia.
    + split; [exact (j2_alias _ _ _ 1 UO U32 Hal ltac:(clear - VO; lia) ltac:(clear - Hhi; lia) ltac:(clear; lia))|].
      split; [exact (j2_alias _ _ _ 2 UO U32 Hal ltac:(clear - VO; lia) ltac:(clear - Hhi; lia) ltac:(clear; lia))|].
      split; [exact (j2_alias _ _ _ 3 UO U32 Hal ltac:(clear - VO; lia) ltac:(clear - Hhi; lia) ltac:(clear; lia))|].
      split; [exact (j2_alias _ _ _ 4 UO U32 Hal ltac:(clear - VO; lia) ltac:(clear - Hhi; lia) ltac:(clear; lia))|].
      split; [exact (j2_alias _ _ _ 5 UO U32 Hal ltac:(clear - VO; lia) ltac:(clear - Hhi; lia) ltac:(clear; lia))|].
      split; [exact (j2_alias _ _ _ 6 UO U32 Hal ltac:(clear - VO; lia) ltac:(clear - Hhi; lia) ltac:(clear; lia))|].
      exact I. }
split.
{ (* the shadow entry of [a4, a4 + 14) *)
  constructor; [|constructor].
  assert (HRA : range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF (SF + V_dp) 64).
  { apply zero_shadow_range; [apply j2_mod8; [exact HF32 | reflexivity] | reflexivity | exact Zd]. }
  apply (shent_ok_of_range SEGS (w_H W2) mem2 (j2_E regs2) j2_Bx 14%nat (SF + V_dp) 64 (SF + V_dp + L2) 0 14 HRA).
  - unfold j2_Bx. rewrite U_SLit. reflexivity.
  - rewrite U_SOff, U14, Z.add_0_r. unfold zcanon, M64. apply Z.mod_small. unfold V_dp.
    clear - HF0 HF1 HL2 C1. lia.
  - clear - HL2. lia.
  - unfold V_dp. clear - HL2. lia.
  - intros x Hx. change (Z.min 0 14) with 0 in Hx. change (Z.max 0 14) with 14 in Hx.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
    clear - Hx HFapp HL2 C1. unfold SHADOW_OFF, V_dp in *. intros Hc. lia. }
split.
{ (* the run writes only the frame (4, pos) *)
  unfold j2_ss. cbn [ss_mem].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 14%nat (SF + V_dp + L2)); [reflexivity | exact U14 | | ].
  - intros a Ha. cbn [j2_rD YP09.r_wlo YP09.r_whi] in Ha. right. right. right.
    exists 4, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. rewrite Efa.
    change (fs_frame_bytes 4) with 1024. clear - Ha HL2 Hi. unfold V_dp in *. lia.
  - apply awr_ok_cons_ro; [cbn; clear; lia|]. apply awr_ok_cons_ro; [cbn; clear; lia|]. apply awr_ok_nil. }
exact U14.
Qed.
(* ---- the exit cut, from the cut at the head and what the run kept and stored ---- *)
Lemma j2_exit : forall (LAWS : AR_laws SEGS B) g pos mf nm tk dp (i : Z) ly2 S2 W2 regs2 mem2 md2 k regs' mem' md',
  AJ g pos ly2 S2 W2 mem' md' k ->
  frames S2 = [(4, pos)] -> 0 <= k <= EV_LLVMF ->
  mo_le MT (e_S g) S2 (k * MEV MT) -> mo_ok MT S2 ((EV_LLVMF - k) * MEV MT) ->
  ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 ->
  jkeep B g pos mf nm tk dp ly2 S2 W2 regs2 mem2 ->
  jdp_regs g pos regs2 ->
  jdp_mem g pos W2 mem2 (j_dp2 (e_pl g) ++ firstn (Z.to_nat i) j_lit_in) ->
  bytes_at8 W2 mem2 (SFa g pos + V_nm) (SlotModel.n_EXP_NM (e_pl g) ++ [RcIdentModel.zb 0]) ->
  getr regs2 27 = w64 (SlotModel.n_ln (e_pl g)) ->
  getr regs2 12 = w64 (j_L2 (e_pl g)) ->
  SlotModel.n_wok (e_pl g) = true ->
  0 <= i < 6 ->
  (forall r, In r j2_KL -> getr regs' r = getr regs2 r) ->
  getr regs' 6 = w64 SHADOW_OFF -> getr regs' 11 = w64 6 ->
  (forall a, 0 <= a < 2 ^ 64 ->
     a < SFa g pos + V_dp + j_L2 (e_pl g) + i \/ SFa g pos + V_dp + j_L2 (e_pl g) + 6 <= a ->
     aview SEGS (w_H W2) mem' a = aview SEGS (w_H W2) mem2 a) ->
  (forall j, (j < 6)%nat -> i <= Z.of_nat j ->
     val_mem SEGS (rd W2 mem') (SFa g pos + V_dp + j_L2 (e_pl g) + Z.of_nat j) 1 (nth j j2_lit 0)) ->
  (forall fd, fd_lookup (m_fds md') fd = fd_lookup (m_fds md2) fd) -> m_fs md' = m_fs md2 ->
  ACUT g pos mf k (BASE + 0x186c)
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       jkeep B g pos mf nm tk dp ly2 S2 W2 regs2 mem2 /\
       jdp_regs g pos regs2 /\ jdp_mem g pos W2 mem2 (j_dp2 (e_pl g) ++ j_lit_in) /\
       bytes_at8 W2 mem2 (SFa g pos + V_nm) (SlotModel.n_EXP_NM (e_pl g) ++ [RcIdentModel.zb 0]) /\
       getr regs2 27 = w64 (SlotModel.n_ln (e_pl g)) /\
       getr regs2 11 = w64 6 /\
       getr regs2 12 = w64 (j_L2 (e_pl g)))
    W2 (cfg_at SEGS (BASE + 0x186c) regs' mem' md').
Proof.
intros LAWS g pos mf nm tk dp i ly2 S2 W2 regs2 mem2 md2 k regs' mem' md' HJ' HFR Hk Hmo Hmok HEC Hkeep Hdpr
  Hdpm Hnm R27 R12 Hwok Hi0 KR R6' R11' K VB Hfd Hfs.
pose proof HEC as (_ & _ & _ & Hmf & _).
destruct (j2_geo LAWS g pos mf ly2 S2 W2 mem' md' k HJ' HFR Hmf)
  as (HAR & Hin4 & Efa & HF0 & HF1 & HFapp & HF32 & Hceil & H47).
pose proof asan_consts as (C1 & _).
pose proof (j2_L2_range _ Hwok) as HL2.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
(* the bytes the run kept *)
assert (KV : forall a n v,
  (forall x, a <= x < a + Z.of_nat n -> 0 <= x < 2 ^ 64 /\
     (x < SFa g pos + V_dp + j_L2 (e_pl g) + i \/ SFa g pos + V_dp + j_L2 (e_pl g) + 6 <= x)) ->
  val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W2 mem') a n v).
{ intros a n v Hx Hv. eapply val_mem_kept; [|exact Hv]. intros kk Hkk.
  destruct (Hx (a + kk) ltac:(clear - Hkk; lia)) as [X1 X2]. exact (K _ X1 X2). }
assert (KG : forall a l,
  (forall x, a <= x < a + Z.of_nat (length l) -> 0 <= x < 2 ^ 64 /\
     (x < SFa g pos + V_dp + j_L2 (e_pl g) + i \/ SFa g pos + V_dp + j_L2 (e_pl g) + 6 <= x)) ->
  garr8 SEGS (rd W2 mem2) a l -> garr8 SEGS (rd W2 mem') a l).
{ intros a l Hx Hg. apply (garr8_frame SEGS _ _ a l Hg). intros x Hxx. apply (mbyte_of_aview SEGS).
  destruct (Hx x Hxx) as [X1 X2]. exact (K x X1 X2). }
assert (KSh : forall s, SHADOW_OFF <= s < SHADOW_OFF + 2 ^ 44 + 256 ->
  aview SEGS (w_H W2) mem' s = aview SEGS (w_H W2) mem2 s).
{ intros s Hs. apply K.
  - unfold SHADOW_OFF in Hs. clear - Hs. lia.
  - clear - Hs HFapp HL2 Hi0. unfold SHADOW_OFF, V_dp in *. lia. }
assert (KZ : forall a n, 0 <= a < 2 ^ 47 -> 0 <= n <= 1024 -> sh_zero W2 mem2 a n -> sh_zero W2 mem' a n).
{ intros a n Ha Hn Hz j Hj. rewrite KSh; [exact (Hz j Hj)|].
  assert (Ha8 : 0 <= a / 8 < 2 ^ 44)
    by (split; [apply Z.div_pos; clear - Ha; lia | apply Z.div_lt_upper_bound; clear - Ha; lia]).
  assert (Hn8 : n / 8 <= 128) by (apply Z.div_le_upper_bound; clear - Hn; lia).
  unfold shadow_of_addr. clear - Ha8 Hn8 Hj. lia. }
assert (KB : forall a n, 0 <= a < 2 ^ 47 -> 0 <= n <= 1024 -> sh_blk W2 mem2 a n -> sh_blk W2 mem' a n).
{ intros a n Ha Hn (Hm & Hn0 & Hb). split; [exact Hm|]. split; [exact Hn0|]. intros j Hj.
  rewrite KSh; [exact (Hb j Hj)|].
  assert (Ha8 : 0 <= a / 8 < 2 ^ 44)
    by (split; [apply Z.div_pos; clear - Ha; lia | apply Z.div_lt_upper_bound; clear - Ha; lia]).
  assert (Hn8 : (n + 7) / 8 <= 129) by (apply Z.div_le_upper_bound; clear - Hn; lia).
  unfold shadow_of_addr. clear - Ha8 Hn8 Hj. lia. }
(* a heap block is apart from the frame (4, pos) *)
assert (KBK : forall b n, In (b, n) (ablocks B ly2 S2) -> 0 <= n ->
  forall x, b <= x < b + n -> 0 <= x < 2 ^ 64 /\
     (x < SFa g pos + V_dp + j_L2 (e_pl g) + i \/ SFa g pos + V_dp + j_L2 (e_pl g) + 6 <= x)).
{ intros b n Hin Hn x Hx.
  destruct (al_blocks _ _ LAWS ly2 S2 W2 mem' md' b n HAR Hin) as (_ & Hb4096 & Hbce & _).
  pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem' md' b n 4 pos HAR Hin Hin4) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Efa in Hd. change (fs_frame_bytes 4) with 1024 in Hd.
  pose proof (req_size_pos n Hn) as Hrq.
  unfold V_dp. clear - Hx Hb4096 Hbce Hd Hrq HL2 Hi0 C1. lia. }
(* a word of the machine stack above mf + 16 *)
assert (VS : forall a v, mf + 16 <= a -> a + 8 <= e_sp0 g ->
  val_mem SEGS (rd W2 mem2) a 8 v -> val_mem SEGS (rd W2 mem') a 8 v).
{ intros a v Ha1 Ha2 Hv. apply KV; [|exact Hv]. intros x Hx. change (Z.of_nat 8) with 8 in Hx.
  unfold V_dp. clear - Hx Ha1 Ha2 Hmf Hceil H47 HF1 HL2 Hi0 C1. lia. }
(* ecommon *)
assert (HEC' : ECOMMON g pos mf ly2 S2 W2 regs' mem' md').
{ pose proof Hkeep as ((Hperm & _) & _).
  unfold ecommon in HEC |- *.
  destruct HEC as (Hsp & Hs1 & Hs0 & Hmf' & Hmf32 & Hgp & Htp & V16 & V64 & V192 & V168 & Vra & Vs0 &
    W9 & W18 & W19 & W20 & W21 & W22 & W23 & W24 & W25 & W26 & W27 & Vfl & HPRE & Hfds & Hfs0 & Hinp).
  assert (Hinb : bytes_at8 W2 mem' (e_p g) (e_pl g)).
  { pose proof HPRE as HP'. unfold e_pre, tLLVMFuzzerTestOneInput_pre in HP'.
    destruct HP' as (_ & _ & _ & _ & Hpn & Hlen & _).
    destruct Hpn as [[Hn0 _] | [Hn Hpin]].
    - unfold bytes_at8. destruct (e_pl g) as [|x l] eqn:Epl; [apply garr8_nil|].
      cbn [length] in Hlen. clear - Hlen Hn0. lia.
    - unfold bytes_at8 in *. apply KG; [|exact Hinp].
      assert (Hin2 : In (e_p g, e_n g) (ablocks B ly2 S2))
        by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; exact Hpin).
      intros x Hx. rewrite length_map, <- Hlen in Hx.
      exact (KBK _ _ Hin2 ltac:(clear - Hn; lia) x Hx). }
  refine (conj _ (conj _ (conj _ (conj Hmf' (conj Hmf32 (conj _ (conj _ _))))))).
  - rewrite (KR 2%bv) by (cbn [In j2_KL]; tauto). exact Hsp.
  - rewrite (KR 9%bv) by (cbn [In j2_KL]; tauto). exact Hs1.
  - rewrite (KR 8%bv) by (cbn [In j2_KL]; tauto). exact Hs0.
  - rewrite (KR 3%bv) by (cbn [In j2_KL]; tauto). exact Hgp.
  - rewrite (KR 4%bv) by (cbn [In j2_KL]; tauto). exact Htp.
  - repeat match goal with
    | |- _ /\ _ => split
    | |- val_mem _ _ (e_sp0 g - _) _ _ => apply VS; [clear - Hmf; lia | clear; lia | assumption]
    | |- val_mem _ _ (mf + _) _ _ => apply VS; [clear; lia | clear - Hmf; lia | assumption]
    | |- val_mem _ _ (_ + 1016) _ _ =>
        apply KV; [intros x Hx; change (Z.of_nat 8) with 8 in Hx;
                   clear - Hx HF0 HF1 HL2 Hi0 C1; unfold V_dp in *; lia | exact Vfl]
    | |- forall fd, _ => intros fd; rewrite Hfd; apply Hfds
    | |- m_fs _ = _ => rewrite Hfs; exact Hfs0
    | |- bytes_at8 _ _ (e_p g) _ => exact Hinb
    | |- _ => exact HPRE
    end. }
(* jkeep *)
assert (Hkeep' : jkeep B g pos mf nm tk dp ly2 S2 W2 regs' mem').
{ destruct Hkeep as (Hhb & Hshr & R24 & R21 & M152 & M184 & M144 & M128 & M120 & M176 & M160 & M112 & Hid & Hnr).
  split; [exact Hhb|].
  split; [unfold sh_reg in *; rewrite (KR 23%bv) by (cbn [In j2_KL]; tauto); exact Hshr|].
  split; [rewrite (KR 24%bv) by (cbn [In j2_KL]; tauto); exact R24|].
  split; [rewrite (KR 21%bv) by (cbn [In j2_KL]; tauto); exact R21|].
  do 8 (split; [apply VS; [clear; lia | clear - Hmf; lia | assumption]|]).
  split.
  - destruct Hid as (Hidb & Hidz & Hidk). split; [|split].
    + unfold bytes_at8 in *. apply KG; [|exact Hidb]. intros x Hx. rewrite length_map in Hx.
      unfold m_id in Hx. rewrite SlotModel.rec_id_length in Hx. change (Z.of_nat RcIdentModel.ID_SIZE) with 38 in Hx.
      clear - Hx HF0 HF1 HL2 Hi0 C1. unfold V_id, V_dp in *. lia.
    + apply KZ; [unfold V_id; clear - HF0 HF1 C1; lia | unfold N_id; clear; lia | exact Hidz].
    + apply KB; [unfold V_id; clear - HF0 HF1 C1; lia | unfold N_id; clear; lia | exact Hidk].
  - intros Hr0. destruct (Hnr Hr0) as (Bn & Bt & Bd).
    destruct (LLVMFuzzerTestOneInput_seg_J_model.m2_fits_r0 _ Hr0) as (_ & Fn & Ft & Fd).
    destruct Hhb as (Hperm & _).
    assert (IB : forall b n, In (b, n) [(nm, Z.max (SlotModel.t_cap_name (e_pl g)) 1);
        (tk, Z.max (SlotModel.t_cap_tok (e_pl g)) 1); (dp, Z.max (SlotModel.t_cap_disp (e_pl g)) 1)] ->
      In (b, n) (ablocks B ly2 S2))
      by (intros b n Hb; apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; left; exact Hb).
    unfold bytes_at8 in *.
    split; [|split].
    + apply KG; [|exact Bn]. intros x Hx. rewrite length_map, length_app in Hx. cbn [length] in Hx.
      apply (KBK nm (Z.max (SlotModel.t_cap_name (e_pl g)) 1)
        (IB nm (Z.max (SlotModel.t_cap_name (e_pl g)) 1) ltac:(cbn [In]; left; reflexivity)) ltac:(clear; lia)).
      unfold SlotModel.n_ln in Fn. clear - Hx Fn. lia.
    + apply KG; [|exact Bt]. intros x Hx. rewrite length_map, length_app in Hx. cbn [length] in Hx.
      apply (KBK tk (Z.max (SlotModel.t_cap_tok (e_pl g)) 1)
        (IB tk (Z.max (SlotModel.t_cap_tok (e_pl g)) 1) ltac:(cbn [In]; right; left; reflexivity)) ltac:(clear; lia)).
      pose proof (j2_n_TK_len (e_pl g)) as LT. clear - Hx Ft LT. lia.
    + apply KG; [|exact Bd]. intros x Hx. rewrite length_map, length_app in Hx. cbn [length] in Hx.
      apply (KBK dp (Z.max (SlotModel.t_cap_disp (e_pl g)) 1)
        (IB dp (Z.max (SlotModel.t_cap_disp (e_pl g)) 1) ltac:(cbn [In]; right; right; left; reflexivity))
        ltac:(clear; lia)).
      unfold SlotModel.n_ld in Fd. clear - Hx Fd. lia. }
(* the registers of exp_dp *)
assert (Hdpr' : jdp_regs g pos regs').
{ destruct Hdpr as (_ & R18 & R25 & R26). split; [exact R6'|].
  split; [rewrite (KR 18%bv) by (cbn [In j2_KL]; tauto); exact R18|].
  split; [rewrite (KR 25%bv) by (cbn [In j2_KL]; tauto); exact R25|].
  rewrite (KR 26%bv) by (cbn [In j2_KL]; tauto). exact R26. }
(* exp_dp, with the literal appended *)
assert (Hdpm' : jdp_mem g pos W2 mem' (j_dp2 (e_pl g) ++ j_lit_in)).
{ destruct Hdpm as (Zn & Zd & Bd).
  split; [apply KZ; [unfold V_nm; clear - HF0 HF1 C1; lia | unfold N_nm; clear; lia | exact Zn]|].
  split; [apply KZ; [unfold V_dp; clear - HF0 HF1 C1; lia | unfold N_dp; clear; lia | exact Zd]|].
  unfold bytes_at8 in *. rewrite map_app in Bd |- *.
  apply (garr8_app SEGS) in Bd as [Bd1 Bd2]. apply (garr8_app SEGS). split.
  - apply KG; [|exact Bd1]. intros x Hx. rewrite length_map, (j2_len_dp2 (e_pl g)) in Hx.
    clear - Hx HF0 HF1 HL2 Hi0 C1. unfold V_dp in *. lia.
  - rewrite length_map in Bd2 |- *. rewrite (j2_len_dp2 (e_pl g)) in Bd2 |- *.
    rewrite j2_map_lit. intros j Hj. unfold j2_lit in Hj. cbn [length] in Hj.
    assert (Hjr : 0 <= nth j j2_lit 0 < 256)
      by (clear - Hj; unfold j2_lit; do 6 (destruct j as [|j]; [cbn [nth]; lia|]); lia).
    split; [|exact Hjr].
    destruct (Z_lt_le_dec (Z.of_nat j) i) as [Hlt | Hge].
    + assert (Hjp : (j < Z.to_nat i)%nat) by (clear - Hlt Hi0; lia).
      destruct (Bd2 j ltac:(rewrite length_map, length_firstn, j2_len_lit; clear - Hjp Hi0; lia)) as [Bv _].
      rewrite (j2_nth_pref (Z.to_nat i) j Hjp ltac:(clear - Hi0; lia)) in Bv.
      apply KV; [|exact Bv]. intros x Hx. change (Z.of_nat 1) with 1 in Hx.
      clear - Hx Hlt Hi0 HF0 HF1 HL2 C1. unfold V_dp in *. lia.
    + exact (VB j ltac:(clear - Hj; lia) Hge). }
(* exp_nm, which the loop does not write *)
assert (Hnm' : bytes_at8 W2 mem' (SFa g pos + V_nm) (SlotModel.n_EXP_NM (e_pl g) ++ [RcIdentModel.zb 0])).
{ unfold bytes_at8 in *. apply KG; [|exact Hnm]. intros x Hx. rewrite length_map, length_app in Hx.
  cbn [length] in Hx. pose proof (SlotModel.n_ln_le _ Hwok) as HLn. unfold SlotModel.n_ln in HLn.
  clear - Hx HLn HF0 HF1 HL2 Hi0 C1. unfold V_nm, V_dp in *. lia. }
unfold acut. exists ly2, S2, regs', mem', md'.
split; [reflexivity|]. split; [exact HJ'|]. split; [exact HFR|]. split; [exact Hk|].
split; [exact Hmo|]. split; [exact Hmok|]. split; [exact HEC'|].
split; [exact Hkeep'|]. split; [exact Hdpr'|]. split; [exact Hdpm'|]. split; [exact Hnm'|].
split; [rewrite (KR 27%bv) by (cbn [In j2_KL]; tauto); exact R27|].
split; [exact R11'|].
rewrite (KR 12%bv) by (cbn [In j2_KL]; tauto). exact R12.
Qed.
(* ---- the loop: one run of the token engine from the head to the exit slot ---- *)
(* The byte the run stored at offset `off` of region 0, read from the final symbolic state. *)
Ltac j2_get HS U14 off v name :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?Ex ?ssF _ =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssF) (YP09.mkRegion None 0 0 0 0 [])) in
      pose proof (j2_chunk Ex ssF _ r0 off v _ HS ltac:(vm_compute; reflexivity) eq_refl U14
        ltac:(cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right])) ltac:(clear; lia)) as name
  end;
  cbn [ms_mem restrict] in name.

Lemma j_lit2 : j_lit2_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS.
Proof.
unfold j_lit2_stmt. intros LAWS g pos mf nm tk dp i W2 c2 HC.
unfold acut in HC.
destruct HC as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & HFR & Hk & Hmo & Hmok & HEC & HP).
destruct HP as (Hpre & Hi & R11 & R12 & R13 & R14 & R15 & R16).
assert (Hi6 : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5) by (clear - Hi; lia).
pose proof HEC as (_ & _ & _ & Hmf & _).
destruct (j2_entry LAWS g pos mf nm tk dp i ly2 S2 W2 regs2 mem2 md2 _ HJ HFR Hmf Hpre Hi Hi6
  R11 R12 R13 R14 R15 R16) as (HS & SHOK & HAW & U14).
pose proof Hpre as (Hkeep & Hdpr & Hdpm & Hnm & R27 & Hwok & _).
assert (HEI : img_env VAL A_LIM (j2_E regs2)) by (unfold j2_E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs2 [Z_to_bv 64 (VAL (A_OBJ 10) / 8)]) (j2_E regs2))
  by (unfold j2_E; split; [intros n Hn; apply Eimg_low; clear - Hn; unfold A_TEXT; lia | reflexivity]).
pose proof (paj_run_to B LAWS) as RUNTO.
pose proof HJ as HJ0.
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 (BASE + 0x1804)) mem2 (seg_rom SEGS))) in HJ0.
unfold cfg_at. change (w64 (BASE + 0x1804)) with (Z_to_bv 64 (BASE + 0x1804)).
clear Hpre.
destruct Hi6 as [-> | [-> | [-> | [-> | [-> | -> ] ] ] ] ].
all: paj_run_to_tok RUNTO HS HJ0 SHOK j2_Bspan 0x186c; [exact HAW |].
all: lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?msx) |- _ => rename msx into msF end.
all: pmkst HS.
all: prreg HS (6%bv : bv 5) N6.
all: prreg HS (11%bv : bv 5) N11.
all: assert (N6' : getr (ms_regs msF) 6 = w64 SHADOW_OFF) by (rewrite N6; reflexivity).
all: assert (N11' : getr (ms_regs msF) 11 = w64 6) by (rewrite N11; reflexivity).
all: pose proof (regs_kept_of_st_ok_pi (j2_E regs2) _ _ regs2 [Z_to_bv 64 (VAL (A_OBJ 10) / 8)] j2_KL HS HAE
       ltac:(vm_compute; reflexivity)) as KR.
all: cbn [ms_regs restrict] in KR.
all: apply SRr_ret.
- pose proof (j2_K (j2_E regs2) 0 _ (w_H W2) mem2 (ms_mem msF) U14 HFr) as K.
  j2_get HS U14 0 32 V0. j2_get HS U14 1 105 V1. j2_get HS U14 2 110 V2. j2_get HS U14 3 32 V3. j2_get HS U14 4 47 V4. j2_get HS U14 5 32 V5.
  assert (VB : forall j, (j < 6)%nat -> 0 <= Z.of_nat j ->
    val_mem SEGS (rd W2 (ms_mem msF)) (SFa g pos + V_dp + j_L2 (e_pl g) + Z.of_nat j) 1 (nth j j2_lit 0)).
  { intros j Hj Hge. do 6 (destruct j as [|j]; [first [exact V0 | exact V1 | exact V2 | exact V3 | exact V4 | exact V5]|]).
    exfalso. clear - Hj. lia. }
  eapply (j2_exit LAWS g pos mf nm tk dp 0 ly2 S2 W2 regs2 mem2 md2 _ (ms_regs msF) (ms_mem msF) _ HJ0 HFR Hk
    Hmo Hmok HEC Hkeep Hdpr Hdpm Hnm R27 R12 Hwok ltac:(clear; lia) KR N6' N11' K VB);
    [intros fd; reflexivity | reflexivity].
- pose proof (j2_K (j2_E regs2) 1 _ (w_H W2) mem2 (ms_mem msF) U14 HFr) as K.
  j2_get HS U14 1 105 V1. j2_get HS U14 2 110 V2. j2_get HS U14 3 32 V3. j2_get HS U14 4 47 V4. j2_get HS U14 5 32 V5.
  assert (VB : forall j, (j < 6)%nat -> 1 <= Z.of_nat j ->
    val_mem SEGS (rd W2 (ms_mem msF)) (SFa g pos + V_dp + j_L2 (e_pl g) + Z.of_nat j) 1 (nth j j2_lit 0)).
  { intros j Hj Hge. do 6 (destruct j as [|j]; [first [exfalso; clear - Hge; lia | exact V1 | exact V2 | exact V3 | exact V4 | exact V5]|]).
    exfalso. clear - Hj. lia. }
  eapply (j2_exit LAWS g pos mf nm tk dp 1 ly2 S2 W2 regs2 mem2 md2 _ (ms_regs msF) (ms_mem msF) _ HJ0 HFR Hk
    Hmo Hmok HEC Hkeep Hdpr Hdpm Hnm R27 R12 Hwok ltac:(clear; lia) KR N6' N11' K VB);
    [intros fd; reflexivity | reflexivity].
- pose proof (j2_K (j2_E regs2) 2 _ (w_H W2) mem2 (ms_mem msF) U14 HFr) as K.
  j2_get HS U14 2 110 V2. j2_get HS U14 3 32 V3. j2_get HS U14 4 47 V4. j2_get HS U14 5 32 V5.
  assert (VB : forall j, (j < 6)%nat -> 2 <= Z.of_nat j ->
    val_mem SEGS (rd W2 (ms_mem msF)) (SFa g pos + V_dp + j_L2 (e_pl g) + Z.of_nat j) 1 (nth j j2_lit 0)).
  { intros j Hj Hge. do 6 (destruct j as [|j]; [first [exfalso; clear - Hge; lia | exact V2 | exact V3 | exact V4 | exact V5]|]).
    exfalso. clear - Hj. lia. }
  eapply (j2_exit LAWS g pos mf nm tk dp 2 ly2 S2 W2 regs2 mem2 md2 _ (ms_regs msF) (ms_mem msF) _ HJ0 HFR Hk
    Hmo Hmok HEC Hkeep Hdpr Hdpm Hnm R27 R12 Hwok ltac:(clear; lia) KR N6' N11' K VB);
    [intros fd; reflexivity | reflexivity].
- pose proof (j2_K (j2_E regs2) 3 _ (w_H W2) mem2 (ms_mem msF) U14 HFr) as K.
  j2_get HS U14 3 32 V3. j2_get HS U14 4 47 V4. j2_get HS U14 5 32 V5.
  assert (VB : forall j, (j < 6)%nat -> 3 <= Z.of_nat j ->
    val_mem SEGS (rd W2 (ms_mem msF)) (SFa g pos + V_dp + j_L2 (e_pl g) + Z.of_nat j) 1 (nth j j2_lit 0)).
  { intros j Hj Hge. do 6 (destruct j as [|j]; [first [exfalso; clear - Hge; lia | exact V3 | exact V4 | exact V5]|]).
    exfalso. clear - Hj. lia. }
  eapply (j2_exit LAWS g pos mf nm tk dp 3 ly2 S2 W2 regs2 mem2 md2 _ (ms_regs msF) (ms_mem msF) _ HJ0 HFR Hk
    Hmo Hmok HEC Hkeep Hdpr Hdpm Hnm R27 R12 Hwok ltac:(clear; lia) KR N6' N11' K VB);
    [intros fd; reflexivity | reflexivity].
- pose proof (j2_K (j2_E regs2) 4 _ (w_H W2) mem2 (ms_mem msF) U14 HFr) as K.
  j2_get HS U14 4 47 V4. j2_get HS U14 5 32 V5.
  assert (VB : forall j, (j < 6)%nat -> 4 <= Z.of_nat j ->
    val_mem SEGS (rd W2 (ms_mem msF)) (SFa g pos + V_dp + j_L2 (e_pl g) + Z.of_nat j) 1 (nth j j2_lit 0)).
  { intros j Hj Hge. do 6 (destruct j as [|j]; [first [exfalso; clear - Hge; lia | exact V4 | exact V5]|]).
    exfalso. clear - Hj. lia. }
  eapply (j2_exit LAWS g pos mf nm tk dp 4 ly2 S2 W2 regs2 mem2 md2 _ (ms_regs msF) (ms_mem msF) _ HJ0 HFR Hk
    Hmo Hmok HEC Hkeep Hdpr Hdpm Hnm R27 R12 Hwok ltac:(clear; lia) KR N6' N11' K VB);
    [intros fd; reflexivity | reflexivity].
- pose proof (j2_K (j2_E regs2) 5 _ (w_H W2) mem2 (ms_mem msF) U14 HFr) as K.
  j2_get HS U14 5 32 V5.
  assert (VB : forall j, (j < 6)%nat -> 5 <= Z.of_nat j ->
    val_mem SEGS (rd W2 (ms_mem msF)) (SFa g pos + V_dp + j_L2 (e_pl g) + Z.of_nat j) 1 (nth j j2_lit 0)).
  { intros j Hj Hge. do 6 (destruct j as [|j]; [first [exfalso; clear - Hge; lia | exact V5]|]).
    exfalso. clear - Hj. lia. }
  eapply (j2_exit LAWS g pos mf nm tk dp 5 ly2 S2 W2 regs2 mem2 md2 _ (ms_regs msF) (ms_mem msF) _ HJ0 HFR Hk
    Hmo Hmok HEC Hkeep Hdpr Hdpm Hnm R27 R12 Hwok ltac:(clear; lia) KR N6' N11' K VB);
    [intros fd; reflexivity | reflexivity].
Qed.

Check (j_lit2 : j_lit2_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
End c.
End b.
End a.
Print Assumptions j_lit2.
