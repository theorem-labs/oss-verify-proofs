(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACes.v:251-253
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AE25.v:79-81 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AE6h.v:80-82 [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC85.v:242-244,
   294-297 [Apache-2.0 OR MIT]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:1255-1258, 1462-1464, 1527-1530, 1556-1561
   [Apache-2.0 OR MIT]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:1749-1752, 1956-1958, 2021-2024, 2050-2055
   [Apache-2.0 OR MIT]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCe5.v:1255-1258, 1462-1464, 1527-1530, 1556-1561
   [Apache-2.0 OR MIT]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCes.v:251-253 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YE25.v:76-78 [Apache-2.0 OR MIT]; projects/cgif/cgif_file_fuzzer/proofs/lib/YE6h.v:76-78
   [Apache-2.0 OR MIT]; projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC04.v:1183-1186, 1391-1393, 1456-1459, 1485-1490
   [Apache-2.0 OR MIT]; projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:145-148, 211-213, 264-266 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YCcz.v:1183-1186, 1391-1393, 1456-1459, 1485-1490 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YCd0.v:145-148, 211-213, 264-266 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YCd1.v:41-44 [Apache-2.0 OR MIT], for libreac/fuzz_identity's ASan build
   (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Piece F of segment J of LLVMFuzzerTestOneInput's ASan walk (fuzz_identity.asan 0x81e18 .. 0x81e60), the statement
   j_F_stmt of LLVMFuzzerTestOneInput_Jcut.v: from Pj4 (exp_nm and exp_dp built, s9 = ln, s2 = ld) to inv_J_end.
     0x81e18 ld a0,152(s1); bgeu s9,a0 -> 0x81e50        ln >= cap_name: not fits
     0x81e20 li a1,'-'; mv a0,s10; mv a2,s9              memchr(exp_nm, '-', ln)
     0x81e2c jal __interceptor_trampoline_memchr          (the contract's AMEMCHR, MemchrDef.v)
     0x81e30 snez a0,a0; sub a0,s9,a0; bgeu a0,s4 -> 0x81e50   lt = ln - (a '-' was found) >= cap_tok: not fits
     0x81e3c ld a1,144(s1); sltu a0,s2,a1                 a0 = ld < cap_disp
     0x81e44 beqz s11 -> 0x81e54; bgeu s2,a1 -> 0x81e54; j 0x822f0 (abort: fits && r != 0)
     0x81e50 li a0,0
     0x81e54 li a1,-1; beq s11,a1 -> 0x81e60; beqz a0 -> 0x822f0 (abort: !fits && r != -1)
   (0x822f0: __asan_handle_no_return, then abort.)
   Each abort is refuted by the plain model (SlotModel.n_r = 0 exactly when n_wok and n_fits; Pj4 has n_wok). The
   segment's only write is memchr's, in its stack window below the machine frame mf; exp_nm, exp_dp, their shadow
   and the machine frame's words are kept. The run is cut at the memchr call and at 0x81e50: each part starts from
   a fresh symbolic state over the concrete registers and memory, and jfrel carries what every part keeps of the
   state at 0x81e18. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String Ascii.
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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentFrame IdentCJ IdentRo
IdentProgSig YC1g YC1h YC45 YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Rt Require Import MemchrDef WrapRo.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require put_dec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec put_dec_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import LLVMFuzzerTestOneInput_Jcut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* YC4b turns lia's division and modulo handling off; the address arithmetic here needs it. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the plain model ------------------------------------------------------------------------------------------ *)
Lemma jf_dec1 : forall x, 0 <= x < 256 -> (length (IdentSpec.DEC x 1) <= 3)%nat.
Proof.
intros x Hx.
assert (H : IdentSpec.z_all (fun y => Nat.leb (length (IdentSpec.DEC y 1)) 3) 256 0 = true) by (vm_compute; reflexivity).
pose proof (IdentSpec.z_all_spec _ 256 0 H x ltac:(lia)) as Hy. cbv beta in Hy. apply Nat.leb_le. exact Hy.
Qed.
(* exp_dp is exp_nm, " (", DEC(in,1), " in / ", DEC(out,1) and " out)": at most 19 bytes more. *)
Lemma jf_ld_le : forall inp, SlotModel.n_ld inp <= SlotModel.n_ln inp + 19.
Proof.
intros inp. unfold SlotModel.n_ld, SlotModel.n_ln, SlotModel.n_EXP_DP. rewrite !length_app.
pose proof (jf_dec1 _ (JModel.tin_range inp)) as D1. pose proof (jf_dec1 _ (JModel.tout_range inp)) as D2.
assert (L1 : length (SlotModel.str_bytes " ("%string) = 2%nat) by reflexivity.
assert (L2 : length (SlotModel.str_bytes " in / "%string) = 6%nat) by reflexivity.
assert (L3 : length (SlotModel.str_bytes " out)"%string) = 5%nat) by reflexivity.
rewrite L1, L2, L3. lia.
Qed.
Lemma jf_r_m1 : forall inp, SlotModel.n_fits inp = false -> SlotModel.n_r inp = -1.
Proof. intros inp H. unfold SlotModel.n_r. rewrite H, andb_false_r. reflexivity. Qed.
Lemma jf_r_0 : forall inp, SlotModel.n_wok inp = true -> SlotModel.n_fits inp = true -> SlotModel.n_r inp = 0.
Proof. intros inp H1 H2. unfold SlotModel.n_r. rewrite H1, H2. reflexivity. Qed.

(* ---- the symbolic values -------------------------------------------------------------------------------------- *)
(* 0x81e30 / 0x81e34: lt = ln - (memchr's result is not 0), with the result 0 exactly when exp_nm has no '-'. *)
Lemma jf_U_lt : forall E (l : list byte) v,
  ew E 25 = w64 (Z.of_nat (length l)) -> ew E 10 = w64 v -> (length l <= 21)%nat -> 0 <= v < 2 ^ 64 ->
  (v =? 0) = negb (SlotModel.has_dash l) ->
  U E (SAlu ALU_SUB (SOff 25 0) (SAlu ALU_SLTU (SLit 0) (SOff 10 0))) =
  Z.of_nat (length l) - (if SlotModel.has_dash l then 1 else 0).
Proof.
intros E l v H25 H10 Hl Hv Hvz.
pose proof (JModel.has_dash_len l) as HDL.
rewrite !U_SAlu. cbn [zalu_raw].
rewrite (U_atom E 25 _ H25) by lia. rewrite (U_atom E 10 v H10 Hv), U_SLit.
change (zcanon 0) with 0.
revert Hvz HDL. destruct (SlotModel.has_dash l); intros Hvz HDL; cbn [negb] in Hvz.
- apply Z.eqb_neq in Hvz. specialize (HDL eq_refl). rewrite (proj2 (Z.ltb_lt 0 v)) by lia.
  unfold zcanon, M64. rewrite (Z.mod_small 1) by lia. apply Z.mod_small. lia.
- apply Z.eqb_eq in Hvz. subst v. rewrite Z.ltb_irrefl. unfold zcanon, M64.
  rewrite (Z.mod_small 0) by lia. rewrite Z.sub_0_r. apply Z.mod_small. lia.
Qed.
Lemma jf_U_sltu : forall E (a b : nat) va vb, ew E a = w64 va -> ew E b = w64 vb -> 0 <= va < 2 ^ 64 -> 0 <= vb < 2 ^ 64 ->
  U E (SAlu ALU_SLTU (SOff a 0) (SOff b 0)) = if va <? vb then 1 else 0.
Proof.
intros E a b va vb Ha Hb Hva Hvb. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E a va Ha Hva), (U_atom E b vb Hb Hvb). destruct (va <? vb); reflexivity.
Qed.

(* lia on the arithmetic facts only (a lia over a walk's whole context is slow): every hypothesis that is not a
   comparison of numbers is cleared first, in a sub-proof. *)
Ltac jf_arith_only :=
  repeat match goal with
  | X : ?T |- _ =>
      lazymatch type of T with
      | Prop =>
          lazymatch T with
          | @eq Z _ _ => fail
          | @eq nat _ _ => fail
          | Z.le _ _ => fail
          | Z.lt _ _ => fail
          | Z.ge _ _ => fail
          | Z.gt _ _ => fail
          | le _ _ => fail
          | lt _ _ => fail
          | not (@eq Z _ _) => fail
          | Z.le _ _ /\ _ => fail
          | Z.lt _ _ /\ _ => fail
          | _ => clear X
          end
      end
  end.
Ltac jfl :=
  match goal with |- ?G =>
    let H := fresh "J" in assert (H : G) by (jf_arith_only; lia); exact H
  end.

(* The registers every part of the segment keeps: ecommon's and jc's, and Pj4's. *)
Definition JF_KEEP : list (bv 5) := [2; 8; 9; 3; 4; 19; 20; 21; 22; 27; 26; 24; 25; 18]%bv.
Lemma jf_pres_keep : forall (regs regs' : bvmap 5 word), aregs_preserved regs regs' ->
  forall r, In r JF_KEEP -> getr regs' r = getr regs r.
Proof.
intros regs regs' HP r Hr. pose proof (HP (bv_unsigned r)) as E. rewrite !Z_to_bv_bv_unsigned in E. apply E.
unfold JF_KEEP in Hr. cbn [In] in Hr. unfold acallee_saved.
repeat (destruct Hr as [<- | Hr];
  [lazymatch goal with |- context [bv_unsigned ?x] =>
     let w := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with w end; lia |]).
destruct Hr.
Qed.

(* The fresh symbolic states: the registers as atoms, and at most one word of the machine frame (base s1 = x9),
   read-only, as atom 32. *)
Definition jf_rg (off : Z) : YP09.region :=
  YP09.mkRegion (Some 9%nat) off (off + 8) (off + 8) (off + 8) [YP09.mkChunk off (CVal 8 (SOff 32 0))].
Definition jf_ss (pc : Z) (rs : smem) : sstate := mkSS pc sr_atoms rs None (mkFacts [] [] []).
(* The writable windows of a run whose regions are all read-only: none. *)
Ltac jf_awr :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' a1 a2 a3 a4 a5 a6 a7) end;
  repeat (apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia|]); apply awr_ok_nil.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation bz := RcIdentModel.bz.
#[local] Notation nthb := RcIdentModel.nthb.
#[local] Notation zb := RcIdentModel.zb.
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).

Lemma jf_bytes_some : forall (W : world SEGS) mem x (l : list byte) a,
  bytes_at8 W mem x l -> x <= a < x + Z.of_nat (length l) -> aview SEGS (w_H W) mem a <> None.
Proof.
intros W mem x l a Hb Ha. unfold bytes_at8 in Hb.
destruct (Hb (Z.to_nat (a - x))) as [Hv Hr]; [rewrite length_map; lia|].
rewrite Z2Nat.id in Hv by lia. replace (x + (a - x)) with a in Hv by lia.
rewrite (aview_of_val_mem1 SEGS (w_H W) mem a _ Hv Hr). discriminate.
Qed.
(* memchr's index of '-' in a NUL-terminated string is below its length exactly when the string has a '-'. *)
Lemma jf_fb_dash : forall (W : world SEGS) mem x (l : list byte) kk,
  bytes_at8 W mem x (l ++ [zb 0]) ->
  first_byte SEGS W mem x (Z.of_nat (length l)) 45 kk ->
  (kk <? Z.of_nat (length l)) = SlotModel.has_dash l.
Proof.
intros W mem x l kk Hb (Hk & Hlt & Hat).
assert (HV : forall j, (j < length l)%nat -> aview SEGS (w_H W) mem (x + Z.of_nat j) = Some (bz (nthb l j))).
{ intros j Hj. unfold bytes_at8 in Hb.
  destruct (Hb j) as [Hv Hr]; [rewrite length_map, length_app; cbn [length]; lia|].
  rewrite (aview_of_val_mem1 SEGS (w_H W) mem _ _ Hv Hr). f_equal.
  rewrite (nth_indep _ 0 (bv_unsigned (zb 0))) by (rewrite length_map, length_app; cbn [length]; lia).
  rewrite (map_nth (fun b : byte => bv_unsigned b)). rewrite app_nth1 by lia. reflexivity. }
unfold SlotModel.has_dash.
destruct (Z.ltb_spec kk (Z.of_nat (length l))) as [Hl | Hg].
- symmetry. apply existsb_exists. exists (nthb l (Z.to_nat kk)). split.
  + unfold nthb. apply nth_In. lia.
  + specialize (Hat Hl). pose proof (HV (Z.to_nat kk) ltac:(lia)) as H. rewrite Z2Nat.id in H by lia.
    rewrite Hat in H. injection H as H. apply Z.eqb_eq. rewrite <- H. reflexivity.
- assert (Hkk : kk = Z.of_nat (length l)) by lia. subst kk.
  symmetry. apply not_true_iff_false. intros Hex. apply existsb_exists in Hex as (b & Hin & Hb45).
  apply (In_nth l b (zb 0)) in Hin as (j & Hj & Hnth).
  destruct (Hlt (Z.of_nat j) ltac:(lia)) as (b' & Hv' & Hne).
  rewrite (HV j Hj) in Hv'. injection Hv' as Hv'. apply Hne. rewrite <- Hv'. unfold nthb. rewrite Hnth.
  apply Z.eqb_eq in Hb45. exact Hb45.
Qed.

Lemma jf_st0 : forall (W : world SEGS) regs mem pc,
  st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (jf_ss pc [])
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros W regs mem pc. rewrite restrict_mkst_fx. unfold jf_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor.
- cbn [pairwise_disjoint all_disjoint]. exact I.
- unfold facts_ok. cbn. split; [exact I | split; exact I].
Qed.
Lemma jf_st1 : forall (W : world SEGS) regs mem pc off mf v,
  regions_wf [jf_rg off] = true ->
  getr regs 9 = w64 mf -> 0 <= mf -> mf + off + 8 <= 2 ^ 64 -> 0 <= off -> 0 <= v < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) mem) (mf + off) 8 v ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [w64 v])) (jf_ss pc [jf_rg off])
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros W regs mem pc off mf v Hwf R9 H0 H1 Hoff Hv HV.
assert (E32 : ew (Eimg (Ereg regs [w64 v])) 32 = w64 v)
  by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (U9 : bv_unsigned (ew (Eimg (Ereg regs [w64 v])) 9) = mf).
{ rewrite (ew_Eimg_Ereg_nat regs _ 9 9%bv eq_refl), R9. apply unsigned_lit_small. lia. }
rewrite restrict_mkst_fx. unfold jf_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- exact Hwf.
- constructor; [|constructor]. unfold jf_rg, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS _ _ mf off 8 (SOff 32 0) v);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
    | lia | lia | exact HV].
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- unfold facts_ok. cbn. split; [exact I | split; exact I].
Qed.

Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
(* The Section of LLVMFuzzerTestOneInput.v / _inv.v, in the same order. *)
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
#[local] Notation ACUT := (acut B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation ECOMMON := (ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation HBLOCKS := (hblocks B).

(* ---- what the segment takes, each as the contract's Section states it (LLVMFuzzerTestOneInput.v) ----------- *)
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis HMT0 : forall s s' : astate, mo_le MT s s' 0.
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Hypothesis HRO : forall rdr, arodata_okS SEGS B RLO RHI rdr -> arodata_okP SEGS pa_relro_lo pa_relro_hi B rdr.
Variable G : list (Z * Z).
Hypothesis GM : globs_marked SEGS B G.
Hypothesis G_IN : In (VAL (A_OBJ 9), 7) G.
Hypothesis G_OUT : In (VAL (A_OBJ 10), 6) G.
Hypothesis G_REAC : In (VAL (A_OBJ 8), 5) G.
Hypothesis HIMG : forall (W : world SEGS) mem,
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> llvmf_img B G W mem.
Hypothesis PSIG : ident_prog_sig_ok (PI := PI).
Hypothesis HPD : put_dec.tput_dec_spec B.
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA IS___interceptor_trampoline_bcmp).
Hypothesis AMEMCHR : amemchr_realizes SEGS B (SIGMA IS___interceptor_trampoline_memchr).
Hypothesis AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
  ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  m_fds md' = m_fds md /\ m_fs md' = m_fs md.

(* ---- the shared layer of segment J (LLVMFuzzerTestOneInput_Jcut.v), at this Section's variables ------------ *)
#[local] Notation jcut := (LLVMFuzzerTestOneInput_Jcut.jcut B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB
  LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation jc := (LLVMFuzzerTestOneInput_Jcut.jc B).
#[local] Notation jcut_mk := (LLVMFuzzerTestOneInput_Jcut.jcut_mk B MT XM_LIB XN_LIB RLO RHI RA_LLVMF A_EMPTY
  LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS MTL HMT0).
#[local] Notation jacut_mono := (LLVMFuzzerTestOneInput_Jcut.jacut_mono B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY
  LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation INV_J := (inv_J_end B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).

(* ---- the bookkeeping ------------------------------------------------------------------------------------------ *)
(* The state at 0x81e18, unfolded from jcut ... (Pj4 g pos mf). *)
Definition jfst (g : ectx) (pos mf nm tk dp : Z) (ly2 : alayout) (S2 : astate) (W2 : world SEGS)
  (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) : Prop :=
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W2 mem2 md2 (4 * Z.of_nat (m_nrec g) + 7) /\
  frames S2 = [(4, pos)] /\ 0 <= 4 * Z.of_nat (m_nrec g) + 7 <= EV_LLVMF /\
  mo_le MT (e_S g) S2 ((4 * Z.of_nat (m_nrec g) + 7) * (mo_malloc MT 256 + mo_free MT)) /\
  mo_ok MT S2 ((EV_LLVMF - (4 * Z.of_nat (m_nrec g) + 7)) * (mo_malloc MT 256 + mo_free MT)) /\
  ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 /\ jc g pos mf nm tk dp ly2 S2 W2 regs2 mem2 /\
  Pj4 g pos mf ly2 S2 W2 regs2 mem2 md2.
(* A later state (regs3, mem3, md3) of the segment: its journal, its memory equal to the start's outside memchr's
   window below mf, and the kept registers. *)
Definition jfrel (g : ectx) (pos mf nm tk dp : Z) (ly2 : alayout) (S2 : astate) (W2 : world SEGS)
  (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model)
  (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) : Prop :=
  jfst g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 /\
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W2 mem3 md3 (4 * Z.of_nat (m_nrec g) + 7) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (mf - ESTACK <= a < mf) -> aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a) /\
  (forall r : bv 5, In r JF_KEEP -> getr regs3 r = getr regs2 r).

Lemma jf_rel_step : forall g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 regs4 mem4 md4,
  jfrel g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 ->
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W2 mem4 md4 (4 * Z.of_nat (m_nrec g) + 7) ->
  (forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) mem4 a = aview SEGS (w_H W2) mem3 a) ->
  (forall r : bv 5, In r JF_KEEP -> getr regs4 r = getr regs3 r) ->
  jfrel g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 regs4 mem4 md4.
Proof.
intros g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 regs4 mem4 md4 (HST & _ & K3 & R3) HJ4 K4 R4.
refine (conj HST (conj HJ4 (conj _ _))).
- intros a Ha Hw. rewrite (K4 a Ha). exact (K3 a Ha Hw).
- intros r Hr. rewrite (R4 r Hr). exact (R3 r Hr).
Qed.

(* ---- 0x81e60: the end ----------------------------------------------------------------------------------------- *)
Lemma jf_close : forall g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3,
  jfrel g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 ->
  SRr SEGS W2 (cfg_at SEGS (BASE + 0x1754) regs3 mem3 md3) (INV_J g pos mf nm tk dp).
Proof.
intros g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 (HST & HJ3 & KEEP & RK).
destruct HST as (HJ2 & Hfr2 & HK & MLE & MOK & HC & HJC & HP).
pose proof (proj1 HJC) as (Hmf0 & Hsp47 & Hsp16 & HSF0 & HSF1 & HSFapp & HSF64 & Hhs & Hinp).
pose proof HC as (_ & _ & _ & Hmfb & _).
pose proof asan_consts as (C1 & _).
destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as [D1 D2].
destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as [D3 D4].
assert (HP3 : Pj4 g pos mf ly2 S2 W2 regs3 mem3 md3).
{ destruct HP as (Hw & R27 & R26 & R24 & R25 & R18 & Hlen & Bnm & Bdp & Snm & Sdp).
  pose proof (jf_ld_le (e_pl g)) as Hld. unfold SlotModel.n_ld, SlotModel.n_ln in Hld.
  assert (TB : forall a bs, 0 <= a -> a + Z.of_nat (length bs) <= SFa g pos + 1024 ->
     bytes_at8 W2 mem2 a bs -> bytes_at8 W2 mem3 a bs).
  { intros a bs Ha0 Ha1 Hb. unfold bytes_at8 in *.
    apply (j_garr8_moved SEGS (w_H W2) (w_H W2) mem2 mem3 a); [|exact Hb].
    intros k Hk. rewrite length_map in Hk.
    apply KEEP; [clear - Ha0 Ha1 Hk HSF1 C1; lia | clear - Ha0 Ha1 Hk HSF1 Hmf0; unfold ESTACK, ASTACK in *; lia]. }
  assert (TS : forall a n, 0 <= a -> a + n <= SFa g pos + 1024 -> 0 <= n ->
     sh_zero W2 mem2 a n -> sh_zero W2 mem3 a n).
  { intros a n Ha0 Ha1 Hn Hz. unfold sh_zero in *.
    apply (j_zero_shadow_moved (aview SEGS (w_H W2) mem2)); [|exact Hz].
    intros i Hi. unfold shadow_of_addr.
    apply KEEP; [clear - Ha0 Ha1 Hn Hi HSF1 C1; unfold SHADOW_OFF; lia
      | clear - Ha0 Ha1 Hn Hi HSF1 Hmf0 C1; unfold ESTACK, ASTACK, SHADOW_OFF in *; lia]. }
  unfold Pj4.
  rewrite (RK 27%bv), (RK 26%bv), (RK 24%bv), (RK 25%bv), (RK 18%bv) by (unfold JF_KEEP; cbn; tauto).
  refine (conj Hw (conj R27 (conj R26 (conj R24 (conj R25 (conj R18 (conj Hlen _))))))).
  refine (conj (TB _ _ _ _ Bnm) (conj (TB _ _ _ _ Bdp) (conj (TS _ _ _ _ _ Snm) (TS _ _ _ _ _ Sdp)))).
  all: unfold V_nm, V_dp, N_nm, N_dp; rewrite ?length_app; cbn [length];
       clear - HSF0 Hlen Hld; lia. }
assert (HJCUT : jcut g pos mf nm tk dp (BASE + 0x1754) (Pj4 g pos mf) W2 (cfg_at SEGS (BASE + 0x1754) regs3 mem3 md3)).
{ apply (jcut_mk g pos mf nm tk dp (BASE + 0x1754) (Pj4 g pos mf) ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 regs3 mem3 md3
    HJ2 Hfr2 HK MLE MOK HC HJC HJ3 Hfr2 (Permutation_refl _)).
  - intros a Ha HW. apply KEEP; [exact Ha|]. intros Hw'. apply HW. unfold WJ. left.
    clear - Hw' Hmf0. unfold ESTACK, ASTACK in *. lia.
  - intros r Hr. apply RK. unfold JF_KEEP. cbn [In] in Hr |- *. tauto.
  - intros fd. rewrite D3, D1. reflexivity.
  - rewrite D4, D2. reflexivity.
  - exact HP3. }
apply SRr_ret. revert HJCUT. unfold LLVMFuzzerTestOneInput_Jcut.jcut, inv_J_end. apply jacut_mono.
intros ly3 S3 W4 r3 m3 d3 _ (HJC3 & HP4).
destruct HJC3 as (_ & _ & _ & Hhb & R20 & R21 & R22 & V184 & V152 & V144 & V160 & V168 & V136 & Hjb).
destruct HP4 as (Hw & R27 & R26 & R24 & _ & _ & _ & Bnm & Bdp & Snm & Sdp).
exact (conj Hhb (conj Hw (conj R27 (conj R26 (conj R24 (conj R20 (conj R21 (conj R22 (conj V184 (conj V152
  (conj V144 (conj V160 (conj V168 (conj V136 (conj Bnm (conj Bdp (conj Snm (conj Sdp Hjb)))))))))))))))))).
Qed.

(* ---- the parts' tactics ----------------------------------------------------------------------------------------- *)
(* The windows of read-only regions are empty. *)
Ltac jf_win :=
  let bb := fresh "jbb" in let wl := fresh "jwl" in let wh := fresh "jwh" in let aa := fresh "jaa" in
  let Hin := fresh "jHin" in let Hr := fresh "jHr" in let Eqw := fresh "jEqw" in
  intros bb wl wh aa Hin Hr; cbn in Hin;
  repeat (destruct Hin as [Eqw|Hin]; [injection Eqw as <- <- <-; cbn [base_val] in Hr; clear - Hr; lia|]);
  destruct Hin.
(* After a run of read-only regions: KM (the current memory equals m0 everywhere) moves to the run's end. *)
Ltac jf_upd KM m0 :=
  lazymatch goal with HFr : frame_of ?E ?rs (mrestrict (w_H ?W) ?m) (mrestrict (w_H ?W) ?m2) |- _ =>
    let K' := fresh "K" in let a := fresh "ja" in let Ha := fresh "jHa" in
    assert (K' : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) m0 a);
    [ intros a Ha;
      rewrite (kept_of_frame (segs := SEGS) E rs (w_H W) m m2 (fun _ : Z => False) HFr ltac:(jf_win) a Ha (fun x => x));
      exact (KM a Ha)
    | clear KM; rename K' into KM;
      repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end ]
  end.
(* The run stopped at the start of a part LEM: the part's state is a jfrel of the segment's start. *)
Ltac jf_into LEM HS HJ HAE HREL KM :=
  let KR := fresh "KR" in
  pose proof (regs_kept_of_st_ok_pi _ _ _ _ _ JF_KEEP HS HAE ltac:(vm_compute; reflexivity)) as KR;
  cbn [ms_regs restrict] in KR;
  pmkst HS;
  eapply LEM; [eapply jf_rel_step; [exact HREL | exact HJ | exact KM | exact KR] | ..].

(* ---- 0x81e50 (not fits, r = -1): a0 = 0, a1 = -1, beq s11,a1 to 0x81e60 ------------------------------------- *)
Lemma jf_1744 : forall g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3,
  jfrel g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 -> SlotModel.n_r (e_pl g) = -1 ->
  SRr SEGS W2 (cfg_at SEGS (BASE + 0x1744) regs3 mem3 md3) (INV_J g pos mf nm tk dp).
Proof.
intros g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 HREL Hr.
pose proof HREL as (HST & HJ & _ & RK).
pose proof HST as (_ & _ & _ & _ & _ & _ & _ & HP).
destruct HP as (_ & R27 & _).
pose proof (SRr_run_to_pi_AJ B LAWS) as RUNTOP. pose proof (SRr_run_pi_AJ B LAWS) as RUNP.
pose proof (paj_branch (PI := PI)) as BR.
pose proof (jf_st0 W2 regs3 mem3 0x1744) as HS. unfold jf_ss in HS.
remember (Eimg (Ereg regs3 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs3 []) E)
  by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E27 : ew E 27 = w64 (-1)).
{ rewrite HE, (ew_Eimg_Ereg_nat regs3 [] 27 27%bv eq_refl), (RK 27%bv) by (unfold JF_KEEP; cbn; tauto).
  rewrite R27, Hr. reflexivity. }
clear HE.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem3 a)
  by (intros; reflexivity).
unfold cfg_at, w64.
paj_run_to_sh RUNTOP HS HJ 0x1754; [jf_awr|]. jf_upd KM mem3.
psrr_branch_pi RUNP BR HS.
- (* r = -1 *)
  clear Hc. paj_run_to_sh RUNTOP HS HJ 0x1754; [jf_awr|]. jf_upd KM mem3.
  jf_into jf_close HS HJ HAE HREL KM.
- (* r <> -1: refuted *)
  exfalso. rewrite branch_eq_U, (jU_off E 27 (-1) 0 E27), U_SLit in Hc. vm_compute in Hc. discriminate Hc.
Qed.

(* ---- 0x81e30, after memchr returned v in a0 (v = 0 exactly when exp_nm has no '-') ------------------------------ *)
Lemma jf_after : forall g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 v,
  jfrel g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 ->
  getr regs3 10 = w64 v -> 0 <= v < 2 ^ 64 ->
  (v =? 0) = negb (SlotModel.has_dash (SlotModel.n_EXP_NM (e_pl g))) ->
  SlotModel.n_ln (e_pl g) < SlotModel.t_cap_name (e_pl g) ->
  SRr SEGS W2 (cfg_at SEGS (BASE + 0x1724) regs3 mem3 md3) (INV_J g pos mf nm tk dp).
Proof.
intros g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 v HREL R10 Hv Hvz Hln.
pose proof HREL as (HST & HJ & KEEP & RK).
pose proof HST as (_ & _ & _ & _ & _ & HC & HJC & HP).
pose proof HC as (_ & Rs1 & _ & Hmfb & _).
pose proof HJC as (Hlay & _ & _ & _ & R20 & _ & _ & _ & _ & V144 & _).
pose proof Hlay as (Hmf0 & Hsp47 & _).
destruct HP as (Hw & R27 & _ & _ & R25 & R18 & Hlen & _).
pose proof asan_consts as (C1 & _).
pose proof (jf_ld_le (e_pl g)) as Hld.
pose proof (JModel.n_r_cases (e_pl g)) as Hrc.
assert (Ccd : 0 <= SlotModel.t_cap_disp (e_pl g) < 64)
  by (unfold SlotModel.t_cap_disp; apply Z.mod_pos_bound; lia).
assert (Cct : 0 <= SlotModel.t_cap_tok (e_pl g) < 40)
  by (unfold SlotModel.t_cap_tok; apply Z.mod_pos_bound; lia).
assert (Hln0 : 0 <= SlotModel.n_ln (e_pl g) <= 21) by (unfold SlotModel.n_ln; lia).
assert (Hld0 : 0 <= SlotModel.n_ld (e_pl g)) by (unfold SlotModel.n_ld; lia).
pose proof (SRr_run_to_pi_AJ B LAWS) as RUNTOP. pose proof (SRr_run_pi_AJ B LAWS) as RUNP.
pose proof (paj_branch (PI := PI)) as BR.
assert (V144' : val_mem SEGS (rd W2 mem3) (mf + 144) 8 (SlotModel.t_cap_disp (e_pl g))).
{ apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem2 mem3 (mf + 144) (mf + 144) 8 _); [|exact V144].
  intros k Hk. apply KEEP; [clear - Hk Hmf0 Hmfb Hsp47 C1; unfold ASTACK in *; lia | clear - Hk; unfold ESTACK; lia]. }
assert (R9 : getr regs3 9 = w64 mf) by (rewrite (RK 9%bv) by (unfold JF_KEEP; cbn; tauto); exact Rs1).
pose proof (jf_st1 W2 regs3 mem3 0x1724 144 mf (SlotModel.t_cap_disp (e_pl g)) ltac:(vm_compute; reflexivity) R9
  ltac:(clear - Hmf0 C1; unfold ASTACK in *; lia) ltac:(clear - Hmfb Hsp47; lia) ltac:(lia) ltac:(lia) V144') as HS.
unfold jf_ss, jf_rg in HS.
remember (Eimg (Ereg regs3 [w64 (SlotModel.t_cap_disp (e_pl g))])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs3 [w64 (SlotModel.t_cap_disp (e_pl g))]) E)
  by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EK : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> In r JF_KEEP -> ew E n = getr regs2 r).
{ intros n r Hn Hr. rewrite HE, (ew_Eimg_Ereg_nat regs3 _ n r Hn). exact (RK r Hr). }
assert (E10 : ew E 10 = w64 v) by (rewrite HE, (ew_Eimg_Ereg_nat regs3 _ 10 10%bv eq_refl); exact R10).
assert (E32 : ew E 32 = w64 (SlotModel.t_cap_disp (e_pl g)))
  by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
clear HE.
assert (E25 : ew E 25 = w64 (SlotModel.n_ln (e_pl g)))
  by (rewrite (EK 25%nat 25%bv eq_refl) by (unfold JF_KEEP; cbn; tauto); exact R25).
assert (E20 : ew E 20 = w64 (SlotModel.t_cap_tok (e_pl g)))
  by (rewrite (EK 20%nat 20%bv eq_refl) by (unfold JF_KEEP; cbn; tauto); exact R20).
assert (E27 : ew E 27 = w64 (SlotModel.n_r (e_pl g)))
  by (rewrite (EK 27%nat 27%bv eq_refl) by (unfold JF_KEEP; cbn; tauto); exact R27).
assert (E18 : ew E 18 = w64 (SlotModel.n_ld (e_pl g)))
  by (rewrite (EK 18%nat 18%bv eq_refl) by (unfold JF_KEEP; cbn; tauto); exact R18).
assert (UA : U E (SAlu ALU_SUB (SOff 25 0) (SAlu ALU_SLTU (SLit 0) (SOff 10 0))) = SlotModel.n_lt (e_pl g))
  by (exact (jf_U_lt E (SlotModel.n_EXP_NM (e_pl g)) v E25 E10 Hlen Hv Hvz)).
assert (U20 : U E (SOff 20 0) = SlotModel.t_cap_tok (e_pl g)) by (apply (U_atom E 20 _ E20); lia).
assert (U18 : U E (SOff 18 0) = SlotModel.n_ld (e_pl g)) by (apply (U_atom E 18 _ E18); lia).
assert (U32 : U E (SOff 32 0) = SlotModel.t_cap_disp (e_pl g)) by (apply (U_atom E 32 _ E32); lia).
assert (U27 : U E (SOff 27 0) = (SlotModel.n_r (e_pl g) + 0) mod M64) by exact (jU_off E 27 _ 0 E27).
assert (USL : U E (SAlu ALU_SLTU (SOff 18 0) (SOff 32 0)) =
  if SlotModel.n_ld (e_pl g) <? SlotModel.t_cap_disp (e_pl g) then 1 else 0)
  by (apply (jf_U_sltu E 18 32 _ _ E18 E32); lia).
clear E10 E20 E25 E27 E18 E32 EK.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem3 a)
  by (intros; reflexivity).
unfold cfg_at, w64.
paj_run_to_sh RUNTOP HS HJ 0x1754; [jf_awr|]. jf_upd KM mem3.
psrr_branch_pi RUNP BR HS.
- (* 0x81e38: lt >= cap_tok, not fits: to 0x81e50 *)
  rewrite branch_geu_U, UA, U20 in Hc. apply negb_true_iff, Z.ltb_ge in Hc.
  assert (Hr : SlotModel.n_r (e_pl g) = -1).
  { apply jf_r_m1. unfold SlotModel.n_fits. rewrite (proj2 (Z.ltb_ge _ _) Hc), andb_false_r. reflexivity. }
  paj_run_to_sh RUNTOP HS HJ 0x1744; [jf_awr|]. jf_upd KM mem3.
  jf_into jf_1744 HS HJ HAE HREL KM. exact Hr.
- rewrite branch_geu_U, UA, U20 in Hc. apply negb_false_iff, Z.ltb_lt in Hc. rename Hc into Hlt.
  paj_run_to_sh RUNTOP HS HJ 0x1754; [jf_awr|]. jf_upd KM mem3.
  psrr_branch_pi RUNP BR HS.
  + (* 0x81e44: r = 0 *)
    rewrite branch_eq_U, U27, U_SLit in Hc. apply Z.eqb_eq in Hc.
    assert (Hr0 : SlotModel.n_r (e_pl g) = 0)
      by (destruct Hrc as [H | H]; [exact H | rewrite H in Hc; vm_compute in Hc; discriminate Hc]).
    clear Hc. paj_run_to_sh RUNTOP HS HJ 0x1754; [jf_awr|]. jf_upd KM mem3.
    psrr_branch_pi RUNP BR HS.
    * exfalso. rewrite branch_eq_U, U27, U_SLit, Hr0 in Hc. vm_compute in Hc. discriminate Hc.
    * clear Hc. paj_run_to_sh RUNTOP HS HJ 0x1754; [jf_awr|]. jf_upd KM mem3.
      psrr_branch_pi RUNP BR HS.
      -- (* 0x81e5c: !fits && r = 0: refuted *)
         exfalso. rewrite branch_eq_U, USL, U_SLit in Hc.
         destruct (JModel.n_r_zero _ Hr0) as [_ Hf]. unfold SlotModel.n_fits in Hf.
         apply andb_true_iff in Hf as [_ Hf3]. rewrite Hf3 in Hc. vm_compute in Hc. discriminate Hc.
      -- clear Hc. paj_run_to_sh RUNTOP HS HJ 0x1754; [jf_awr|]. jf_upd KM mem3.
         jf_into jf_close HS HJ HAE HREL KM.
  + (* r <> 0, so r = -1 *)
    rewrite branch_eq_U, U27, U_SLit in Hc. apply Z.eqb_neq in Hc.
    assert (Hr1 : SlotModel.n_r (e_pl g) = -1)
      by (destruct Hrc as [H | H]; [exfalso; apply Hc; rewrite H; reflexivity | exact H]).
    clear Hc. paj_run_to_sh RUNTOP HS HJ 0x1754; [jf_awr|]. jf_upd KM mem3.
    psrr_branch_pi RUNP BR HS.
    * (* 0x81e48: ld >= cap_disp, not fits *)
      clear Hc. paj_run_to_sh RUNTOP HS HJ 0x1754; [jf_awr|]. jf_upd KM mem3.
      psrr_branch_pi RUNP BR HS.
      -- clear Hc. paj_run_to_sh RUNTOP HS HJ 0x1754; [jf_awr|]. jf_upd KM mem3.
         jf_into jf_close HS HJ HAE HREL KM.
      -- exfalso. rewrite branch_eq_U, U27, U_SLit, Hr1 in Hc. vm_compute in Hc. discriminate Hc.
    * (* 0x81e4c: fits && r != 0: refuted *)
      exfalso. rewrite branch_geu_U, U18, U32 in Hc. apply negb_false_iff in Hc.
      assert (Hf : SlotModel.n_fits (e_pl g) = true).
      { unfold SlotModel.n_fits. rewrite (proj2 (Z.ltb_lt _ _) Hln), (proj2 (Z.ltb_lt _ _) Hlt), Hc. reflexivity. }
      rewrite (jf_r_0 _ Hw Hf) in Hr1. discriminate Hr1.
Qed.

(* ---- memchr through the contract's AMEMCHR, at a state of a journal ------------------------------------------- *)
Lemma jf_memchr_at : forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x c n (o : Z) raw,
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  getr regsT 10 = w64 x -> getr regsT 11 = w64 c -> getr regsT 12 = w64 n ->
  0 <= c < 256 -> 0 <= n < 2 ^ 32 -> 0 < x -> x + n <= 2 ^ 63 ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  src_ok SEGS W regsT memT x n -> amem_range x n ->
  range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF x n ->
  (0 < n -> shadow_hull_vis (aview SEGS (w_H W) memT) x n) ->
  aro_unowned SEGS B (aview SEGS (w_H W) memT) ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA IS___interceptor_trampoline_memchr)) memT (seg_rom SEGS)) mdc)
  (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
     c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
     ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
     aregs_preserved regsT regs2 /\
     (exists kk, first_byte SEGS W memT x n c kk /\ getr regs2 10 = (if kk <? n then w64 (x + kk) else w64 0)) /\
     (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - ESTACK <= a < sp0 + o) ->
        aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
     (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x c n o raw
  HJ Ha0 Ha1 Ha2 Hc Hn Hx0 Hxn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hsrc Hamr Hras Hhull Hrom.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HPRE : ecall_pre SEGS B lyc Sc W regsT memT mdc).
{ eapply ecall_pre_at with (o := o); try eassumption. rewrite Hra. exact Hraw. }
eapply SRr_mono.
{ exact (AMEMCHR lyc Sc W regsT memT mdc x c n HPRE Ha0 Ha1 Ha2 Hc Hn Hx0 Hxn Hsrc Hamr Hras Hhull Hrom). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write SEGS B LAWS pa_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
    (fun a => sp0 + o - ESTACK <= a < sp0 + o) Sc own HJ).
  - intros a Ha Hna. apply (Hfr a Ha). exact Hna.
  - exact Hpres2.
  - exact Hsame.
  - intros a Ha; left; left; lia.
  - exact HAR2.
  - reflexivity. - reflexivity. - lia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfr | exact Hpres2].
Qed.

(* rget: a register of a state the symbolic run reached, as the run's symbolic value. *)
Ltac jf_rget HS r H :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict ?Hh ?ms) =>
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in
      pose proof (st_ok_restrict_reg segs Hh E ss ms r HS) as H;
      change (sr_get (ss_regs ss) r) with e in H
  end.

(* ---- piece F: 0x81e18 .. 0x81e60 -------------------------------------------------------------------------------- *)
Theorem j_F : j_F_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none
  ameta_inv arodata_okS.
Proof.
intros g pos mf nm tk dp W2 c2 Hstart.
destruct Hstart as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & HK & MLE & MOK & HC & HJC & HP).
assert (HST : jfst g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2)
  by exact (conj HJ (conj Hfrs (conj HK (conj MLE (conj MOK (conj HC (conj HJC HP))))))).
assert (HREL : jfrel g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 regs2 mem2 md2)
  by exact (conj HST (conj HJ (conj (fun a _ _ => eq_refl) (fun r _ => eq_refl)))).
pose proof HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & Rs3 & V80 & V192 & V176 & Vra & Vs0 &
  V24 & V32 & V40 & V48 & V56 & V64 & V72 & V80b & V88 & V96 & V104 & Vmf24 & Vflag & HPRE & Hfds & Hfss & Hinb).
clear V80 V192 V176 Vra Vs0 V24 V32 V40 V48 V56 V64 V72 V80b V88 V96 V104 Vmf24 Vflag Hfds Hfss Hinb.
pose proof HJC as (Hlay & _ & _ & _ & R20 & _ & _ & _ & V152 & _).
pose proof Hlay as (Hmf0 & Hsp47 & Hsp16 & HSF0 & HSF1 & HSFapp & HSF64 & _ & _).
pose proof HP as (Hw & R27 & R26 & R24 & R25 & R18 & Hlen & Bnm & Bdp & Snm & Sdp).
clear Bdp Sdp.
pose proof asan_consts as (C1 & _).
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
unfold e_pre, tLLVMFuzzerTestOneInput_pre in HPRE.
destruct HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAROS & _).
assert (Ccn : 0 <= SlotModel.t_cap_name (e_pl g) < 40)
  by (unfold SlotModel.t_cap_name; apply Z.mod_pos_bound; lia).
assert (Hln0 : 0 <= SlotModel.n_ln (e_pl g) <= 21) by (unfold SlotModel.n_ln; lia).
pose proof (SRr_run_to_pi_AJ B LAWS) as RUNTOP. pose proof (SRr_run_pi_AJ B LAWS) as RUNP.
pose proof (SRr_run_pi_AJ_call B LAWS) as RUNC. pose proof (paj_branch (PI := PI)) as BR.
pose proof (jf_st1 W2 regs2 mem2 0x170c 152 mf (SlotModel.t_cap_name (e_pl g)) ltac:(vm_compute; reflexivity) Rs1
  ltac:(clear - Hmf0 C1; unfold ASTACK in *; lia) ltac:(clear - Hmfb Hsp47; lia) ltac:(lia) ltac:(lia) V152) as HS.
unfold jf_ss, jf_rg in HS.
remember (Eimg (Ereg regs2 [w64 (SlotModel.t_cap_name (e_pl g))])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs2 [w64 (SlotModel.t_cap_name (e_pl g))]) E)
  by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E25 : ew E 25 = w64 (SlotModel.n_ln (e_pl g))) by (rewrite HE, (ew_Eimg_Ereg_nat regs2 _ 25 25%bv eq_refl); exact R25).
assert (E26 : ew E 26 = w64 (SFa g pos + V_nm)) by (rewrite HE, (ew_Eimg_Ereg_nat regs2 _ 26 26%bv eq_refl); exact R26).
assert (E32 : ew E 32 = w64 (SlotModel.t_cap_name (e_pl g)))
  by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
clear HE.
assert (U25 : U E (SOff 25 0) = SlotModel.n_ln (e_pl g)) by (apply (U_atom E 25 _ E25); lia).
assert (U26 : U E (SOff 26 0) = SFa g pos + V_nm)
  by (apply (U_atom E 26 _ E26); unfold V_nm; clear - HSF0 HSF1 C1; lia).
assert (U32 : U E (SOff 32 0) = SlotModel.t_cap_name (e_pl g)) by (apply (U_atom E 32 _ E32); lia).
clear E25 E26 E32.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W2) mem2 a)
  by (intros; reflexivity).
unfold cfg_at, w64.
paj_run_to_sh RUNTOP HS HJ 0x1744; [jf_awr|]. jf_upd KM mem2.
psrr_branch_pi RUNP BR HS.
- (* 0x81e1c: ln >= cap_name, not fits: to 0x81e50 *)
  rewrite branch_geu_U, U25, U32 in Hc. apply negb_true_iff, Z.ltb_ge in Hc.
  assert (Hr : SlotModel.n_r (e_pl g) = -1).
  { apply jf_r_m1. unfold SlotModel.n_fits. rewrite (proj2 (Z.ltb_ge _ _) Hc). reflexivity. }
  paj_run_to_sh RUNTOP HS HJ 0x1744; [jf_awr|]. jf_upd KM mem2.
  jf_into jf_1744 HS HJ HAE HREL KM. exact Hr.
- rewrite branch_geu_U, U25, U32 in Hc. apply negb_false_iff, Z.ltb_lt in Hc. rename Hc into Hln.
  paj_run_shc RUNP RUNC HS HJ; [jf_awr|]. jf_upd KM mem2.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?m) => rename m into msC end.
  pose proof (regs_kept_of_st_ok SEGS _ _ _ _ _ JF_KEEP HS HAE ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  jf_rget HS (10%bv : bv 5) Ra0. jf_rget HS (11%bv : bv 5) Ra1. jf_rget HS (12%bv : bv 5) Ra2.
  jf_rget HS (1%bv : bv 5) Rra.
  assert (Rsp' : spZ (ms_regs msC) = mf).
  { unfold spZ. rewrite (KR 2%bv) by (unfold JF_KEEP; cbn; tauto). rewrite Rsp. unfold w64.
    apply unsigned_lit_small. clear - Hmf0 Hmfb Hsp47 C1; unfold ASTACK in *; lia. }
  (* what memchr reads: the ln bytes of exp_nm, their shadow, the frame's shadow hull, the read-only image *)
  assert (BnmT : bytes_at8 W2 (ms_mem msC) (SFa g pos + V_nm) (SlotModel.n_EXP_NM (e_pl g) ++ [zb 0])).
  { unfold bytes_at8 in *. apply (j_garr8_moved SEGS (w_H W2) (w_H W2) mem2 (ms_mem msC)); [|exact Bnm].
    intros k Hk. apply KM. rewrite length_map, length_app in Hk. cbn [length] in Hk.
    unfold V_nm. clear - Hk Hlen HSF0 HSF1 C1. lia. }
  assert (SnmT : zero_shadow (aview SEGS (w_H W2) (ms_mem msC)) SHADOW_OFF (SFa g pos + V_nm) 32).
  { apply (j_zero_shadow_moved (aview SEGS (w_H W2) mem2)); [|exact Snm].
    intros i Hi. apply KM. unfold shadow_of_addr, V_nm, SHADOW_OFF. clear - Hi HSF0 HSF1 C1. lia. }
  pose proof HJ as (HART & HlyT & _).
  pose proof HlyT as (_ & _ & _ & _ & _ & EF & _).
  assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
  assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
  pose proof (HRO _ HAROS) as HROe.
  pmkst HS.
  eapply SRr_bind.
  { eapply (jf_memchr_at W2 (ms_regs msC) (ms_mem msC) LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g)
      (e_md g) [(4, pos)] ly2 S2 _ (4 * Z.of_nat (m_nrec g) + 7) (SFa g pos + V_nm) 45 (SlotModel.n_ln (e_pl g))
      (mf - e_sp0 g) (Z_to_bv 64 (BASE + 0x1724)) HJ).
    - rewrite Ra0, jsv_U, U26. reflexivity.
    - rewrite Ra1. reflexivity.
    - rewrite Ra2, jsv_U, U25. reflexivity.
    - lia.
    - clear - Hln0. lia.
    - unfold V_nm. clear - HSF0. lia.
    - unfold V_nm. clear - Hln0 HSF0 HSF1 C1. lia.
    - rewrite Rsp'. lia.
    - clear - Hmf32 Hsp16. lia.
    - clear - Hmfb. lia.
    - clear - Hmfb HSTK'. unfold ESTACK, ASTACK in *. lia.
    - rewrite (KR 3%bv) by (unfold JF_KEEP; cbn; tauto). exact Rgp.
    - rewrite (KR 4%bv) by (unfold JF_KEEP; cbn; tauto). exact Rtp.
    - rewrite Rra. exact (codeptr_val E 0x1724 HEI).
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - intros a Ha. rewrite Rsp'. split.
      + apply (jf_bytes_some W2 (ms_mem msC) _ _ a BnmT). rewrite length_app. cbn [length].
        unfold SlotModel.n_ln in Ha. clear - Ha. lia.
      + unfold V_nm in Ha. clear - Ha Hln0 HSF1 Hmf0. unfold ESTACK, ASTACK in *. lia.
    - apply (amem_range_sub_app (SFa g pos) 1024); [exact HSFapp | exact HSF1 | unfold V_nm; lia
        | unfold V_nm; clear - Hln0; lia | lia].
    - apply (range_addressable_sub _ _ (SFa g pos + V_nm) 32); [| lia | clear - Hln0; lia].
      apply zero_shadow_range; [unfold V_nm; clear - HSF64; lia | reflexivity | exact SnmT].
    - intros Hn0. apply (shadow_hull_vis_of_frame SEGS B LAWS ly2 S2 W2 (ms_mem msC) _ 4 pos _ _ HART Hin4);
        [rewrite EFa; unfold V_nm; lia | rewrite EFa; change (fs_frame_bytes 4) with 1024; unfold V_nm;
         clear - Hln0; lia | exact Hn0].
    - exact (aro_unowned_of_arodata SEGS _ _ B _
        (arodata_ok_journalP SEGS _ _ pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HROe)). }
  cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & (kk & Hfb & Ha03) & Hfr3 & Hpres3).
  assert (Hdash : (kk <? SlotModel.n_ln (e_pl g)) = SlotModel.has_dash (SlotModel.n_EXP_NM (e_pl g)))
    by exact (jf_fb_dash W2 (ms_mem msC) _ _ kk BnmT Hfb).
  assert (HREL3 : jfrel g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3).
  { refine (conj HST (conj HJ3 (conj _ _))).
    - intros a Ha Hwin. rewrite (Hfr3 a Ha) by (clear - Hwin; lia). exact (KM a Ha).
    - intros r Hr. rewrite (jf_pres_keep _ _ HP3 r Hr). exact (KR r Hr). }
  pose proof Hfb as (Hk0 & _).
  revert Ha03 Hdash. destruct (Z.ltb_spec kk (SlotModel.n_ln (e_pl g))) as [Hkl | Hkg]; intros Ha03 Hdash.
  + apply (jf_after g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 (SFa g pos + V_nm + kk) HREL3 Ha03).
    * unfold V_nm. clear - Hkl Hk0 Hln0 HSF0 HSF1 C1. lia.
    * rewrite <- Hdash. cbn [negb]. apply Z.eqb_neq. unfold V_nm. clear - Hk0 HSF0. lia.
    * exact Hln.
  + apply (jf_after g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 0 HREL3 Ha03).
    * lia.
    * rewrite <- Hdash. reflexivity.
    * exact Hln.
Qed.
End c.
End b.
End a.
