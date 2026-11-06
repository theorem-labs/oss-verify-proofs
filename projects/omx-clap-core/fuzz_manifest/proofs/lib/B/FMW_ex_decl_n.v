(* G4.ExDecl, IMAGE B: dseg_N and dseg_J (FMW_ex_decl_base.v), B's shared return block of the declaration scan
   (no 1:1 A twin: A has EX_CONT 0x814dc `s3 += 1` instead). From B's code (fm_b_expected_iface.out lines 275-280):
     0x81690 EX_JUMP  sub s7, a1, a6        s7 = (text + j) - text = j
     0x81694 EX_NEXT  addi s7, s7, 1        s7 = j + 1
     0x81698          add s5, a6, s7        s5 = text + j + 1
     0x8169c          ld a0, 0x80(sp)       a0 = F+0x80 = ~text
     0x816a0          bgeu a0, s7, -0x2e0   -> EX_L 0x813c0; not taken: 0x816a4 j -> the UBSan trap 0x8194c
   The guard 0x816a0 (B5 class K1n) is refuted by text + j + 1 < 2^64: the run's facts give ~text a range above
   2^64 - 2^47 and j + 1 one below 2^47 + 1, so the executor decides the bgeu taken. EX_L's invariant ex_at_L at
   j + 1 then holds: s7 = j + 1, s5 = text + j + 1, every other register and the memory as at the cut. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YFen.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC20 YI16 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v YCeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMPstat FMH_Base FMH_Rt FMH_Fn FMW_lib FMTrapB.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_ex_base FMW_ex_decl_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel expected_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* EX_NEXT's symbolic state: the registers as atoms; the slot F+0x80 = ~text as extra atom 32 (no write window);
   the facts that decide the guard: ~text above 2^64 - 2^47, j (atom 23) below 2^47 *)
Definition n_frame : YP09.region := YP09.mkRegion (Some 2%nat) 0x80 0x88 0x80 0x80 (dd_slot_chunks [(0x80, 0%nat)]).
Definition ss_N : sstate :=
  mkSS EX_NEXT sr_atoms [n_frame] None
    (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (23%nat, mkAF 0 (2 ^ 47) 0);
              (32%nat, mkAF (2 ^ 64 - 2 ^ 47) (2 ^ 64 - 1) 0)] [] []).
(* EX_JUMP's: the registers as atoms, no memory *)
Definition ss_J : sstate := mkSS EX_JUMP sr_atoms [] None (mkFacts [] [] []).

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

Lemma n_entry : forall cx j d f ly3 S3 W3 regs3 mem3 md3,
  dat_N B cx j d f ly3 S3 W3 regs3 mem3 md3 ->
  st_ok tfibsegs (Ereg regs3 [w64 (2 ^ 64 - 1 - cx_t cx)]) ss_N
    (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 EX_NEXT) mem3 (seg_rom tfibsegs))).
Proof.
  intros cx j d f ly3 S3 W3 regs3 mem3 md3 (HB & HC & HSL & HSR & HCR & HSC & R23).
  pose proof (dd_bounds B cx HB) as (HFm & HFlo & HFhi & Ht4 & Htc & Hu4 & Huc).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (FS : STK_expected = 8464) by reflexivity.
  pose proof HSC as (Hj & _).
  destruct HC as (_ & _ & _ & Rsp & _).
  destruct HSL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & S80).
  rewrite restrict_mkst_fx.
  set (E := Ereg regs3 [w64 (2 ^ 64 - 1 - cx_t cx)]).
  assert (U2 : bv_unsigned (ew E 2) = cx_F cx)
    by (subst E; rewrite (ew_Ereg_nat regs3 _ 2 2%bv eq_refl), Rsp; apply unsigned_lit_small; lia).
  assert (U23 : bv_unsigned (ew E 23) = Z.of_nat j)
    by (subst E; rewrite (ew_Ereg_nat regs3 _ 23 23%bv eq_refl), R23; apply unsigned_lit_small; lia).
  assert (E32 : ew E 32 = w64 (2 ^ 64 - 1 - cx_t cx)) by (subst E; exact (ew_Ereg_extra regs3 _ 0)).
  assert (U32 : bv_unsigned (ew E 32) = 2 ^ 64 - 1 - cx_t cx)
    by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
  unfold ss_N. apply (entry_st_ok_full tfibsegs); change (Ereg regs3 [w64 (2 ^ 64 - 1 - cx_t cx)]) with E.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, n_frame.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U2.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply dd_chunks_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd Nat.add].
    rewrite U32. exact S80.
  - cbn. tauto.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U23, U32. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat split; first [exact HFm | lia].
Qed.

Theorem decl_N_holds : dseg_N B.
Proof.
  intros cx i j d f ly3 S3 W3 regs3 mem3 md3 HLf Hij HD.
  pose proof LAWS as HL. pose proof fmw_segs_low as Hsegs. pose proof fmw_wx as Hwx.
  pose proof (n_entry cx j d f ly3 S3 W3 regs3 mem3 md3 HD) as HS.
  destruct HD as (HB & HC & HSL & HSR & HCR & HSC & R23).
  pose proof (dd_bounds B cx HB) as (HFm & HFlo & HFhi & Ht4 & Htc & Hu4 & Huc).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (FS : STK_expected = 8464) by reflexivity.
  pose proof HC as (HJ & _).
  pose proof HCR as (R16 & R17 & R5 & R6).
  pose proof HSR as (R19 & R27 & R8).
  pose proof HSC as (Hj & _).
  set (E := Ereg regs3 [w64 (2 ^ 64 - 1 - cx_t cx)]) in *.
  assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr regs3 q)
    by (intros n q Hn; subst E; apply ew_Ereg_nat; exact Hn).
  assert (E23 : ew E 23 = w64 (Z.of_nat j)) by (rewrite (EE 23%nat 23%bv eq_refl); exact R23).
  assert (E16 : ew E 16 = w64 (cx_t cx)) by (rewrite (EE 16%nat 16%bv eq_refl); exact R16).
  assert (E17 : ew E 17 = w64 6) by (rewrite (EE 17%nat 17%bv eq_refl); exact R17).
  assert (E5 : ew E 5 = w64 58) by (rewrite (EE 5%nat 5%bv eq_refl); exact R5).
  assert (E6 : ew E 6 = w64 EX_MASK1) by (rewrite (EE 6%nat 6%bv eq_refl); exact R6).
  assert (E19 : ew E 19 = w64 5) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
  assert (E27 : ew E 27 = w64 32) by (rewrite (EE 27%nat 27%bv eq_refl); exact R27).
  assert (E8 : ew E 8 = w64 (2 ^ 64 - 1)) by (rewrite (EE 8%nat 8%bv eq_refl); exact R8).
  clearbody E.
  assert (SHOK : sh_ok tfibsegs EX_Bx [] E
    (mrestrict (w_H W3) (ms_mem (mkst regs3 (Z_to_bv 64 EX_NEXT) mem3 (seg_rom tfibsegs))))) by constructor.
  assert (AV : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W3) mem3 a)
    by reflexivity.
  change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 EX_NEXT) mem3 (seg_rom tfibsegs))) in HJ.
  unfold cfg_at. change (w64 EX_NEXT) with (Z_to_bv 64 EX_NEXT).
  (* 0x81694 .. 0x816a0: s7 = j + 1, s5 = text + s7, a0 = ~text; the guard bgeu decided taken -> EX_L *)
  aj_run_to_tok EX_tbl_ok HS HJ SHOK EX_Bspan EX_L.
  { awr_ok_tac. }
  dd_av W3 mem3. dd_mk HS.
  apply (HLf (S j) d f ly3 S3 W3 _ _ _ ltac:(lia)).
  split; [exact HB|].
  split.
  { apply (dd_com_kept B cx ly3 S3 W3 regs3 mem3 md3 _ _ _ HB HC HJ); [intros a Ha _ _ _; exact (AV a Ha)|..];
      dd_g HS; apply EE; reflexivity. }
  split; [apply (dd_slots_kept cx W3 mem3 _ d HSL); intros a Ha _; apply AV; lia|].
  split; [split; [|split]; dd_g HS; assumption|].
  split; [split; [|split; [|split]]; dd_g HS; assumption|].
  split; [exact HSC|].
  split; dd_regs HS EE.
Qed.

Theorem decl_J_holds : dseg_J B.
Proof.
  intros cx i j d f ly3 S3 W3 regs3 mem3 md3 HLf Hij HD.
  pose proof LAWS as HL. pose proof fmw_segs_low as Hsegs. pose proof fmw_wx as Hwx.
  destruct HD as (HB & HC & HSL & HSR & HCR & HSC & R11).
  pose proof (dd_bounds B cx HB) as (HFm & HFlo & HFhi & Ht4 & Htc & Hu4 & Huc).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (FS : STK_expected = 8464) by reflexivity.
  pose proof HC as (HJ & _).
  pose proof HCR as (R16 & R17 & R5 & R6).
  pose proof HSR as (R19 & R27 & R8).
  pose proof HSC as (Hj & _).
  assert (HS : st_ok tfibsegs (Ereg regs3 []) ss_J
    (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 EX_JUMP) mem3 (seg_rom tfibsegs)))).
  { rewrite restrict_mkst_fx. unfold ss_J. apply (entry_st_ok_full tfibsegs).
    - apply regs_ok_Ereg.
    - reflexivity.
    - apply Forall_nil.
    - exact I.
    - split; [exact I | split; exact I]. }
  set (E := Ereg regs3 []) in *.
  assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr regs3 q)
    by (intros n q Hn; subst E; apply ew_Ereg_nat; exact Hn).
  assert (E11 : ew E 11 = w64 (cx_t cx + Z.of_nat j)) by (rewrite (EE 11%nat 11%bv eq_refl); exact R11).
  assert (E16 : ew E 16 = w64 (cx_t cx)) by (rewrite (EE 16%nat 16%bv eq_refl); exact R16).
  assert (E17 : ew E 17 = w64 6) by (rewrite (EE 17%nat 17%bv eq_refl); exact R17).
  assert (E5 : ew E 5 = w64 58) by (rewrite (EE 5%nat 5%bv eq_refl); exact R5).
  assert (E6 : ew E 6 = w64 EX_MASK1) by (rewrite (EE 6%nat 6%bv eq_refl); exact R6).
  assert (E19 : ew E 19 = w64 5) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
  assert (E27 : ew E 27 = w64 32) by (rewrite (EE 27%nat 27%bv eq_refl); exact R27).
  assert (E8 : ew E 8 = w64 (2 ^ 64 - 1)) by (rewrite (EE 8%nat 8%bv eq_refl); exact R8).
  clearbody E.
  assert (SHOK : sh_ok tfibsegs EX_Bx [] E
    (mrestrict (w_H W3) (ms_mem (mkst regs3 (Z_to_bv 64 EX_JUMP) mem3 (seg_rom tfibsegs))))) by constructor.
  assert (AV : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W3) mem3 a)
    by reflexivity.
  change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 EX_JUMP) mem3 (seg_rom tfibsegs))) in HJ.
  unfold cfg_at. change (w64 EX_JUMP) with (Z_to_bv 64 EX_JUMP).
  (* 0x81690 sub s7, a1, a6: s7 = j; then EX_NEXT *)
  aj_run_to_tok EX_tbl_ok HS HJ SHOK EX_Bspan EX_NEXT.
  { awr_ok_tac. }
  dd_av W3 mem3. dd_mk HS.
  apply (decl_N_holds cx i j d f ly3 S3 W3 _ _ _ HLf Hij).
  split; [exact HB|].
  split.
  { apply (dd_com_kept B cx ly3 S3 W3 regs3 mem3 md3 _ _ _ HB HC HJ); [intros a Ha _ _ _; exact (AV a Ha)|..];
      dd_g HS; apply EE; reflexivity. }
  split; [apply (dd_slots_kept cx W3 mem3 _ d HSL); intros a Ha _; apply AV; lia|].
  split; [split; [|split]; dd_g HS; assumption|].
  split; [split; [|split; [|split]]; dd_g HS; assumption|].
  split; [exact HSC|].
  dd_regs HS EE.
Qed.
End W.

Check decl_N_holds.
Check decl_J_holds.
Print Assumptions decl_J_holds.
