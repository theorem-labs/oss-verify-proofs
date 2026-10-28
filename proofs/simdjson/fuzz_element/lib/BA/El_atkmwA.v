From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_defsA Atp_kitA Atp_objkA El_callsA El_atkmdA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).
Local Ltac pre_ok l ::= lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?n) _ _ _ _) =>
  let b := eval vm_compute in (andb (andb (Z.leb 736088 n) (Z.ltb n 737124)) (negb (existsb (Z.eqb n) l))) in
  lazymatch b with true => idtac end end.

Definition atkm_set_site (ra' code : Z) : Prop := (ra' = 0xb3c90 /\ code = 17) \/ (ra' = 0xb3cec /\ code = 20).

Lemma atkm_forget : forall (m : mem) (A DOC out P : Z) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word),
  rw_cells asegs m A (atkm_frame DOC out P ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  rw_cells asegs m A ([CB 8 (le8 (wz DOC)); CB 8 (le8 (wz out)); C8 (wz P)] ++ atkm_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
Proof.
  intros m A DOC out P ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 H. eapply rw_cells_recastA; [exact H| |reflexivity].
  cbn [atkm_saved app cells_wf cell_wf]. repeat split; apply length_le8.
Qed.

Lemma atkm_shz_keep : forall (m m' : mem) (q out : Z), shz m out 24 -> munch [(q + -128, q); (out, out + 24)] m m' ->
  0x7fff7f800000 <= q + -128 -> q <= out -> out + 24 <= 0x800000000000 -> shz m' out 24.
Proof.
  intros m m' q out SH MU HQ QO OH x Hx. unfold shz in SH. specialize (SH x Hx). cbn [ov_read_bytes] in SH |- *.
  assert (E1 : m' (wa (x / 8 + 2147450880)) = m (wa (x / 8 + 2147450880))).
  { apply MU. unfold wa. rewrite unsigned_lit; [|Z.div_mod_to_equations; lia]. cbn [outside]. Z.div_mod_to_equations. repeat split; lia. }
  rewrite E1. exact SH.
Qed.

Section AtKmWalks.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.
  Variable d : nat.

  Definition atkm_rx (q out RA : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (c : list cell) : machine_state -> Prop :=
    fun ms => exists (m' : mem) (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
      munch [(q + -128, q); (out, out + 24)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' (ae_lo E) q /\
      rw_cells asegs m' out c /\
      ms = MS (mkR (wz RA) (wz q) gp (wz TPV) y5 y6 y7 s0 s1 y10 y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
              F (ret_pc (wz RA)) fc None m' (seg_rom asegs).

  Lemma atkm_epi : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (q P RA : Z)
      (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (j0 j1 : list byte)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    rw_cells asegs m (q + -128) ([CB 8 j0; CB 8 j1; C8 (wz P)] ++ atkm_saved (wz RA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    stk asegs m (ae_lo E) (q + -128) -> mem_inv asegs m -> ae_lo E <= q + -128 ->
    (forall (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word), stk asegs m (ae_lo E) q ->
       K (MS (mkR (wz RA) (wz q) gp (wz TPV) y5 y6 y7 s0 s1 y10 y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
             F (ret_pc (wz RA)) fc None m (seg_rom asegs))) ->
    evt asegs K (MS (mkR x1 (wz (q + -128)) gp (wz TPV) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                         x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                    F (wz 0xb3d04) fc None m (seg_rom asegs)).
  Proof.
    intros until x31. intros FR ST MI LO HK. unfold atkm_saved in FR. cbn [app] in FR.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
    do 13 step. step.
    release_frame FR ST q.
    step. apply evt_done. apply HK. exact ST.
  Qed.

  Lemma atkm_set_ret : forall (m : mem) (F : bvmap 5 word) (fc : bv 32) (q out P RA ra' code : Z)
      (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (j0 j1 zb oc od : list byte)
      (x5 x6 x7 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 : word),
    rw_cells asegs m (q + -128) ([CB 8 j0; CB 8 j1; C8 (wz P)] ++ atkm_saved (wz RA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    stk asegs m (ae_lo E) (q + -128) -> mem_inv asegs m -> ae_lo E <= q + -128 ->
    rw_cells asegs m out [CB 16 zb; CB 4 oc; CB 4 od] -> q <= out -> out + 24 <= ae_hi E -> out mod 8 = 0 ->
    shz m out 24 -> 0 <= RA < 2^64 -> atkm_set_site ra' code ->
    evt asegs (atkm_rx q out RA gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m [CB 16 zb; C4 (wz code); CB 4 od])
               (MS (mkR (wz ra') (wz (q + -128)) gp (wz TPV) x5 x6 x7 xs0 (wz (out + 16)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                        xs2 xs3 (wz 2147450880) xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)
                   F (wz ra') fc None m (seg_rom asegs)).
  Proof using OK.
    intros until x31. intros FR ST MI LO OUT QO OB O8 SHZO RA0 SITE.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT.
    pose proof (munch_refl [(q + -128, q); (out, out + 24)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold atkm_saved in FR. cbn [app] in FR.
    destruct SITE as [(-> & ->)|(-> & ->)];
      (chk0 SHZO (out + 16); step; if_false; runl [0xb3d04];
       name_mem m1; eapply atkm_epi; [exact FR| exact ST| exact MI| exact LO|];
       intros until y31; intros ST';
       unfold atkm_rx; exists m1, y5, y6, y7, y10, y11, y12, y13, y14, y15, y16, y17, y28, y29, y30, y31;
       split; [exact MU|]; split; [exact WM|]; split; [exact MI|]; split; [exact ST'|]; split; [exact OUT|reflexivity]).
  Qed.

  Lemma atkm_found : forall (m : mem) (F : bvmap 5 word) (fc : bv 32) (q out P RA it : Z)
      (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (oa ob oc od : list byte)
      (x1 x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 : word),
    rw_cells asegs m (q + -128) (atkm_frame (ae_DOC E) out P (wz RA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    stk asegs m (ae_lo E) (q + -128) -> mem_inv asegs m -> ae_lo E <= q + -128 ->
    rw_cells asegs m out [CB 8 oa; CB 8 ob; CB 4 oc; CB 4 od] -> q <= out -> out + 24 <= ae_hi E -> out mod 8 = 0 ->
    shz m out 24 -> 0 <= RA < 2^64 -> 0 <= it -> it + 1 < 2^63 ->
    evt asegs (atkm_rx q out RA gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m
                        [C8 (wz (ae_DOC E)); C8 (wz (it + 1)); C4 (wz 0); CB 4 od])
               (MS (mkR x1 (wz (q + -128)) gp (wz TPV) x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                        (wz it) xs3 (wz 2147450880) xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)
                   F (wz 0xb3e8c) fc None m (seg_rom asegs)).
  Proof using OK.
    intros until x31. intros FR ST MI LO OUT QO OB O8 SHZO RA0 IT0 ITH.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT.
    pose proof (munch_refl [(q + -128, q); (out, out + 24)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold atkm_frame, atkm_saved in FR. cbn [app] in FR.
    shz_at SHZO out. run.
    pose proof (atkm_shz_keep m _ q out SHZO MU ltac:(lia) QO ltac:(lia)) as SH1.
    shz_at SH1 (out + 8). run.
    pose proof (atkm_shz_keep m _ q out SHZO MU ltac:(lia) QO ltac:(lia)) as SH2.
    shz_at SH2 (out + 16). runl [0xb3d04].
    name_mem mf.
    pose proof (atkm_forget mf (q + -128) (ae_DOC E) out P (wz RA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR) as FR'.
    eapply atkm_epi; [exact FR'| exact ST| exact MI| exact LO|].
    intros until y31. intros ST'.
    unfold atkm_rx. exists mf, y5, y6, y7, y10, y11, y12, y13, y14, y15, y16, y17, y28, y29, y30, y31.
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST'|]. split; [exact OUT|reflexivity].
  Qed.

End AtKmWalks.
