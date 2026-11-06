(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics StackLayout Fs State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Mem Cells Step Frame PropExec MState.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require MainExport MainFactsAsan MainEntry.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AImg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Notation.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import StackInit InitLib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import LinZ InitAsanLib RootAsan2.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St LinZ InitAsanLib.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module InitAsan2.
Import RootAsan2.
Module MXm := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS.MainExport.
Module MFm := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS.MainFactsAsan.
Module AMm := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module AFm := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame.
Module ASTm := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState.
Module MEm := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS.MainEntry.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition PH : PhdrInfo := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg.a_phdrs.
Definition PCN : N := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg.a_init_pc.
Definition SEGTOP : Z := 0x62f000.
Lemma segs_top : InitLib.segs_below SEGS SEGTOP = true. Proof. vm_compute. reflexivity. Qed.
Lemma segtop_low : SEGTOP <= 0x7fff7f800000. Proof. cbv. discriminate. Qed.

Section Main.
Variable xb0 : int -> list byte.
Variables (sp : word) (argv envp : list (list byte)) (uid hwcap : word) (draw : EntryDraw).
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Hypothesis Hhw : valid_hwcap hwcap.
Hypothesis Hargc2 : length argv = 2%nat.
Let usp : Z := bv_unsigned sp.
Let argc : Z := Z.of_nat (length argv).
Let envc : Z := Z.of_nat (length envp).

Variables (V : nat -> Z) (m : word -> option byte).
Hypothesis HV : forall n, 0 <= V n < 2 ^ 64.
Hypothesis Pusp : 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat = usp.
Hypothesis Pargc : V 1%nat = argc.
Hypothesis Penvc : V 2%nat = envc.
Hypothesis Pa0 : V 3%nat = Z.of_nat (length (nth 0 argv [])).
Hypothesis Pwblk : V 4%nat = (Z.of_nat (length (build_stack_bytes PH sp argv envp uid hwcap draw)) - 16
                              - (8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 184)) / 8.
Hypothesis Puid : V 8%nat = bv_unsigned uid.
Hypothesis Phw : V 9%nat = bv_unsigned hwcap.
Hypothesis Ptid : 1 <= V 44%nat <= 4194303.
Hypothesis HMF : Forall (MXm.mfact_ok SEGS V m) MFm.asan_mem_facts.
Hypothesis Hminv : AMm.mem_inv SEGS m.

Definition E0 : env := InitLib.E0 sp argv envp uid hwcap draw xb0.

Fixpoint opq_get (l : list (int * nat)) (k : int) : option nat :=
  match l with [] => None | kn :: r => if PrimInt63.eqb k (fst kn) then Some (snd kn) else opq_get r k end.
Definition evA (k : int) : word :=
  match opq_get OPQ k with
  | Some n => Z_to_bv 64 (V n)
  | None => match base_of DER k with Some l => Z_to_bv 64 (leval V l) | None => ev E0 k end
  end.
Definition egA (k : int) (o : Z) : byte :=
  match rb SEGS m (bv_unsigned (evA k) + o) with Some b => b | None => Z_to_bv 8 0 end.
Definition E : env := Env evA (eb E0) egA.

Lemma kv_ok : LinZ.kv_ok V KV.
Proof. unfold KV. constructor; [|constructor]. cbn [fst snd]. rewrite Pargc. unfold argc. rewrite Hargc2. reflexivity. Qed.

Lemma ubv : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N]. apply Z.mod_small. exact Hz. Qed.

Lemma a0_nth : nth 0 argv [] = hd [] argv. Proof. destruct argv; reflexivity. Qed.

Lemma wblk_val : Z.of_nat (SI.raw_len argv envp + SI.pad argv envp) = Z.of_nat (SI.sstruct argv envp) + 8 * V 4%nat.
Proof.
  pose proof (InitLib.len_BSB PH sp argv envp uid hwcap draw) as HL. pose proof (InitLib.sstruct_val PH sp argv envp uid hwcap draw) as HS.
  destruct (InitLib.pad_spec PH sp argv envp uid hwcap draw) as [q Hq].
  unfold SI.BSB in HL. unfold SI.raw_len in *. unfold SI.argcZ, SI.envcZ, SI.nargc, SI.nenvc in HS.
  rewrite !Nat2Z.inj_add in *.
  assert (D : (Z.of_nat (length (build_stack_bytes PH sp argv envp uid hwcap draw)) - 16
               - (8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 184)) / 8
              = q - 23 - Z.of_nat (length argv) - Z.of_nat (length envp)).
  { symmetry. apply (Z.div_unique _ 8 _ 0); lia. }
  rewrite Pwblk, D. lia.
Qed.

Lemma OPQ_first : forallb (fun kn => match opq_get OPQ (fst kn) with Some n => Nat.eqb n (snd kn) | None => false end) OPQ = true.
Proof. vm_compute. reflexivity. Qed.

Lemma HB : Forall (fun kb => bv_unsigned (ev E (fst kb)) = leval V (snd kb)) B.
Proof.
  pose proof (InitLib.sstruct_val PH sp argv envp uid hwcap draw) as HS. unfold SI.argcZ, SI.envcZ, SI.nargc, SI.nenvc in HS.
  assert (A2 : Z.of_nat (length argv) = 2) by (rewrite Hargc2; reflexivity).
  unfold B. apply Forall_app. split; [|apply Forall_app; split].
  - unfold BSTD. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd ev E]; unfold leval; cbn [fst snd lsum].
    + change (evA 0%uint63) with (ev E0 0%uint63). unfold E0. rewrite InitLib.ev0_0. reflexivity.
    + change (evA 1%uint63) with (ev E0 1%uint63). unfold E0. rewrite InitLib.ev0_1. fold usp. lia.
    + change (evA 2%uint63) with (ev E0 2%uint63). unfold E0. rewrite (InitLib.ev0_2 PH sp argv envp uid hwcap draw xb0 Hva Hve Hsp Hfit).
      unfold SI.envp_off, SI.argcZ, SI.nargc, SI.SP. fold usp. lia.
    + change (evA 3%uint63) with (ev E0 3%uint63). unfold E0. rewrite (InitLib.ev0_3 PH sp argv envp uid hwcap draw xb0 Hsp Hfit).
      unfold SI.auxv_off, SI.argcZ, SI.envcZ, SI.nargc, SI.nenvc, SI.SP. fold usp. fold envc. lia.
    + change (evA 5%uint63) with (ev E0 5%uint63). unfold E0. rewrite (InitLib.ev0_5 PH sp argv envp uid hwcap draw xb0 Hfit).
      unfold SI.SP. fold usp. fold envc in HS. lia.
    + change (evA 6%uint63) with (ev E0 6%uint63). unfold E0. rewrite (InitLib.ev0_6 PH sp argv envp uid hwcap draw xb0 Hfit).
      rewrite wblk_val. unfold SI.SP. fold usp. fold envc in HS. lia.
    + change (evA 7%uint63) with (ev E0 7%uint63). unfold E0. rewrite InitLib.ev0_7. lia.
    + change (evA 8%uint63) with (ev E0 8%uint63). unfold E0. rewrite InitLib.ev0_8. lia.
    + change (evA 10%uint63) with (ev E0 10%uint63). unfold E0. rewrite (InitLib.ev0_10 PH sp argv envp uid hwcap draw xb0 Hva Hsp Hfit).
      rewrite <- a0_nth, <- Pa0. unfold SI.SP. fold usp. fold envc in HS. lia.
  -
    pose proof (InitLib.f_sp_range PH sp argv envp uid hwcap draw xb0 Hva Hve Hsp Hfit) as F. cbn [fact_holds] in F.
    rewrite InitLib.ev0_1 in F. fold usp in F. change (w2Z (wp 140735340871680%uint63)) with 140735340871680 in F.
    change (w2Z (wp 140737488355112%uint63)) with 140737488355112 in F.
    pose proof (HV 0%nat) as R0. pose proof (HV 6%nat) as R6. pose proof (HV 10%nat) as R10.
    unfold DER. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd ev E];
      match goal with |- bv_unsigned (evA ?k) = leval V ?l => change (evA k) with (Z_to_bv 64 (leval V l)) end;
      rewrite ubv; first [reflexivity | unfold leval; cbn [fst snd lsum]; lia].
  - apply Forall_forall. intros kb Hkb. apply in_map_iff in Hkb as (kn & <- & Hkn). cbn [fst snd ev E].
    pose proof (proj1 (forallb_forall _ _) OPQ_first kn Hkn) as F. cbv beta in F. unfold evA.
    destruct (opq_get OPQ (fst kn)) as [n|]; [|discriminate]. apply Nat.eqb_eq in F. subst n.
    rewrite (ubv _ (HV _)). rewrite leval_lvar. reflexivity.
Qed.

Lemma HNF : Forall (nfact_ok SEGS V m) NFS.
Proof.
  assert (EN : NFS = map (norm_fact KV) MFm.asan_mem_facts) by (vm_compute; reflexivity).
  rewrite EN. apply Forall_forall. intros f Hf. apply in_map_iff in Hf as (f0 & <- & Hf0).
  apply (norm_fact_sound SEGS V m KV kv_ok). exact (proj1 (Forall_forall _ _) HMF f0 Hf0).
Qed.

Hypothesis Hstk : AFm.stk SEGS m (usp - 8388608) usp.
Local Notation mem0 := (SI.mem0 SEGS PCN PH sp argv envp uid hwcap draw).

Hypothesis Hhid : forall a,
  (usp + 8 * argc + 16 <= a < usp + 8 * argc + 8 * envc + 24) \/
  (usp + 8 * argc + 8 * envc + 184 <= a < usp + 8 * argc + 8 * envc + 184 + 8 * V 4%nat) ->
  m (Z_to_bv 64 a) = mem0 (Z_to_bv 64 a).

Lemma usp_range : 0x7fff80000000 <= usp <= 0x7fffffffff28.
Proof.
  pose proof (InitLib.f_sp_range PH sp argv envp uid hwcap draw xb0 Hva Hve Hsp Hfit) as F. cbn [fact_holds] in F.
  rewrite InitLib.ev0_1 in F. fold usp in F. exact F.
Qed.

Lemma ev1 : bv_unsigned (ev E 1%uint63) = usp.
Proof. change (ev E 1%uint63) with (ev E0 1%uint63). unfold E0. rewrite InitLib.ev0_1. reflexivity. Qed.

Lemma noseg : forall a, SEGTOP <= a -> find_segment SEGS a 1 = None.
Proof. intros a Ha. apply (InitLib.find_segment_none SEGS a 1 SEGTOP segs_top); lia. Qed.

Lemma R0_bst : IMap.bst (rg_cells R0). Proof. unfold R0. cbn [rg_cells]. apply InitLib.imap_of_bst. Qed.
Lemma R1_bst : IMap.bst (rg_cells R1). Proof. unfold R1. cbn [rg_cells]. apply InitLib.imap_of_bst. Qed.
Lemma R3_bst : IMap.bst (rg_cells R3). Proof. unfold R3. cbn [rg_cells]. apply InitLib.imap_of_bst. Qed.
Lemma ev0A : ev E 0%uint63 = Z_to_bv 64 0.
Proof. change (ev E 0%uint63) with (ev E0 0%uint63). unfold E0. apply InitLib.ev0_0. Qed.

Lemma R0_ok : region_ok SEGS PRIV E m 0%uint63 R0.
Proof. exact (region0_ok SEGS V m E B HB NFS HNF PRIV R0 R0_bst eq_refl ev0A Hminv R0_cells_ok COVER COVER_tags_ok COVER_sweep_ok). Qed.

Lemma R1_cov : range_covered_b R1 0 24 = true. Proof. vm_compute. reflexivity. Qed.
Lemma R3_cov : range_covered_b R3 0 160 = true. Proof. vm_compute. reflexivity. Qed.

Lemma R1_valid : forall a, usp + -8384512 <= a < usp + 24 ->
  rb SEGS m a <> None /\ (rg_w R1 = true -> wb SEGS m a = true) /\ find_segment SEGS a 1 = None.
Proof.
  intros a Ha. pose proof usp_range as U. assert (NS : find_segment SEGS a 1 = None) by (apply noseg; unfold SEGTOP; lia).
  destruct (Z.lt_ge_cases a usp) as [Hl|Hg].
  - destruct Hstk as (_ & _ & Hs). destruct (Hs a ltac:(lia)) as [Hw (b & Hb)].
    split; [rewrite rb_mrd; unfold AM.wa; unfold AMm.wa in Hb; rewrite Hb; discriminate|]. split; [|exact NS].
    intros _. unfold wb. unfold AMm.wa in Hw. destruct (wview SEGS m (Z_to_bv 64 a)); [reflexivity| contradiction].
  - assert (R : rb SEGS m a <> None).
    { pose proof (range_covered_rb SEGS V m E B HB NFS HNF 1%uint63 R1 (-8384512) 24 R1_cells_ok 0 24 R1_cov (a - usp) ltac:(lia)) as X.
      rewrite ev1 in X. replace (usp + (a - usp)) with a in X by lia. exact X. }
    split; [exact R|]. split; [|exact NS]. intros _. apply (wb_of_rb_noseg SEGS m a); [lia| exact R| exact NS].
Qed.

Lemma R1_ok : region_ok SEGS PRIV E m 1%uint63 R1.
Proof.
  pose proof usp_range as U.
  apply (based_region_ok SEGS V m E B HB NFS HNF PRIV 1%uint63 R1 (-8384512) 24 eq_refl R1_bst eq_refl eq_refl).
  - rewrite ev1. lia.
  - rewrite ev1. rewrite two64_eq. lia.
  - rewrite ev1. exact R1_valid.
  - exact R1_cells_ok.
  -
    intros o Ho _. unfold bg_byte. change (rg_bg R1) with BGNone. exact I.
Qed.

Lemma ev3 : bv_unsigned (ev E 3%uint63) = usp + 8 * envc + 40.
Proof.
  change (ev E 3%uint63) with (ev E0 3%uint63). unfold E0. rewrite (InitLib.ev0_3 PH sp argv envp uid hwcap draw xb0 Hsp Hfit).
  unfold SI.auxv_off, SI.argcZ, SI.envcZ, SI.nargc, SI.nenvc, SI.SP. fold usp. fold envc. rewrite Hargc2. lia.
Qed.
Lemma envc_range : 0 <= envc <= 256.
Proof. pose proof (SI.envc_range envp Hve) as H. unfold SI.envcZ, SI.nenvc in H. exact H. Qed.

Lemma R3_ok : region_ok SEGS PRIV E m 3%uint63 R3.
Proof.
  pose proof usp_range as U. pose proof envc_range as EC.
  apply (based_region_ok SEGS V m E B HB NFS HNF PRIV 3%uint63 R3 0 160 eq_refl R3_bst eq_refl eq_refl).
  - rewrite ev3. lia.
  - rewrite ev3. rewrite two64_eq. lia.
  - rewrite ev3. intros a Ha. split; [|split].
    + pose proof (range_covered_rb SEGS V m E B HB NFS HNF 3%uint63 R3 0 160 R3_cells_ok 0 160 R3_cov (a - (usp + 8 * envc + 40)) ltac:(lia)) as X.
      rewrite ev3 in X. replace (usp + 8 * envc + 40 + (a - (usp + 8 * envc + 40))) with a in X by lia. exact X.
    + intros W. discriminate W.
    + apply noseg. unfold SEGTOP. lia.
  - exact R3_cells_ok.
  - intros o Ho _. exact I.
Qed.

Lemma hid_agree : forall a,
  (usp + 8 * argc + 16 <= a < usp + 8 * argc + 8 * envc + 24) \/
  (usp + 8 * argc + 8 * envc + 184 <= a < usp + 8 * argc + 8 * envc + 184 + 8 * V 4%nat) ->
  rb SEGS m a = rb SEGS mem0 a /\ (wb SEGS mem0 a = true -> wb SEGS m a = true).
Proof. intros a Ha. unfold rb, wb, wview. rewrite (Hhid a Ha). split; [reflexivity| intros W; exact W]. Qed.

Lemma sstructZ : Z.of_nat (SI.sstruct argv envp) = 8 * argc + 8 * envc + 184.
Proof. pose proof (InitLib.sstruct_val PH sp argv envp uid hwcap draw) as HS. unfold SI.argcZ, SI.envcZ, SI.nargc, SI.nenvc in HS. fold argc envc in HS. lia. Qed.
Lemma strZ : Z.of_nat (SI.total_nat argv) + Z.of_nat (SI.total_nat envp) + Z.of_nat (SI.pad argv envp) = 8 * V 4%nat.
Proof. pose proof wblk_val as W. unfold SI.raw_len in W. rewrite !Nat2Z.inj_add in W. lia. Qed.

Lemma R2_okA : region_ok SEGS PRIV E m 2%uint63 InitLib.R2T.
Proof.
  apply (region_ok_transfer SEGS [] PRIV E0 E mem0 m 2%uint63 InitLib.R2T eq_refl
           (InitLib.R2_ok SEGS PCN PH SEGTOP segs_top segtop_low sp argv envp uid hwcap draw xb0 Hva Hve Hsp Hfit)).
  - reflexivity.
  - reflexivity.
  - intros g gr c F. cbn in F. discriminate F.
  - intros o Ho. reflexivity.
  - intros a Ha. apply hid_agree. left.
    unfold E0 in Ha. rewrite (InitLib.ev0_2 PH sp argv envp uid hwcap draw xb0 Hva Hve Hsp Hfit) in Ha.
    rewrite (InitLib.hiZ_R2 PH sp argv envp uid hwcap draw xb0 Hve) in Ha. rewrite (InitLib.loZ_0 InitLib.R2T eq_refl) in Ha.
    unfold SI.envp_off, SI.argcZ, SI.envcZ, SI.nargc, SI.nenvc, SI.SP in Ha. fold usp argc envc in Ha. lia.
Qed.

Lemma R5_okA : region_ok SEGS PRIV E m 5%uint63 InitLib.R5T.
Proof.
  apply (region_ok_transfer SEGS [] PRIV E0 E mem0 m 5%uint63 InitLib.R5T eq_refl
           (InitLib.R5_ok SEGS PCN PH SEGTOP segs_top segtop_low sp argv envp uid hwcap draw xb0 Hva Hsp Hfit)).
  - reflexivity.
  - reflexivity.
  - intros g gr c F. cbn in F. discriminate F.
  - intros o Ho. reflexivity.
  - intros a Ha. apply hid_agree. right.
    unfold E0 in Ha. rewrite (InitLib.ev0_5 PH sp argv envp uid hwcap draw xb0 Hfit) in Ha.
    rewrite (InitLib.hiZ_R5 PH sp argv envp uid hwcap draw xb0 Hva) in Ha. rewrite (InitLib.loZ_0 InitLib.R5T eq_refl) in Ha.
    pose proof (InitLib.total_ge_a0 PH sp argv envp uid hwcap draw Hva) as T. pose proof strZ as SZ. pose proof sstructZ as SS.
    unfold SI.SP in Ha. fold usp in Ha. lia.
Qed.

Lemma R10_okA : region_ok SEGS PRIV E m 10%uint63 InitLib.R10T.
Proof.
  apply (region_ok_transfer SEGS [] PRIV E0 E mem0 m 10%uint63 InitLib.R10T eq_refl
           (InitLib.R10_ok SEGS PCN PH SEGTOP segs_top segtop_low sp argv envp uid hwcap draw xb0 Hva Hsp Hfit Hargc2)).
  - reflexivity.
  - reflexivity.
  - intros g gr c F. cbn in F. discriminate F.
  - intros o Ho. reflexivity.
  - intros a Ha. apply hid_agree. right.
    unfold E0 in Ha. rewrite (InitLib.ev0_10 PH sp argv envp uid hwcap draw xb0 Hva Hsp Hfit) in Ha.
    rewrite (InitLib.hiZ_R10 SEGS PCN PH sp argv envp uid hwcap draw xb0 Hva Hfit Hargc2) in Ha. rewrite (InitLib.loZ_0 InitLib.R10T eq_refl) in Ha.
    pose proof (InitLib.total2 SEGS PCN PH sp argv envp uid hwcap draw Hva Hfit Hargc2) as T. pose proof strZ as SZ. pose proof sstructZ as SS.
    unfold SI.SP in Ha. fold usp in Ha. lia.
Qed.

Lemma R12_okA : region_ok SEGS PRIV E m 12%uint63 InitLib.R12T.
Proof.
  apply (region_ok_transfer SEGS [] PRIV E0 E mem0 m 12%uint63 InitLib.R12T eq_refl
           (InitLib.R12_ok SEGS PCN PH SEGTOP segs_top segtop_low sp argv envp uid hwcap draw xb0 Hsp Hfit)).
  - reflexivity.
  - reflexivity.
  - intros g gr c F. cbn in F. discriminate F.
  - intros o Ho. reflexivity.
  - intros a Ha. apply hid_agree. right.
    unfold E0 in Ha. rewrite (InitLib.ev0_12 PH sp argv envp uid hwcap draw xb0 Hfit) in Ha.
    rewrite (InitLib.hiZ_R12 PH sp argv envp uid hwcap draw xb0 Hsp Hfit) in Ha. rewrite (InitLib.loZ_0 InitLib.R12T eq_refl) in Ha.
    rewrite (InitLib.strarea_len PH sp argv envp uid hwcap draw) in Ha. pose proof strZ as SZ. pose proof sstructZ as SS.
    unfold SI.SP in Ha. fold usp in Ha. lia.
Qed.

Local Ltac CLOSE := first [eassumption | exact PH | exact SEGS | exact PCN | exact SEGTOP | exact segs_top | exact segtop_low].
Lemma facts_E0 : facts_hold E0 FACTS.
Proof.
  unfold E0, FACTS, facts_hold. repeat apply Forall_cons; try apply Forall_nil.
  - unshelve (eapply InitLib.f_sp_le_auxv); CLOSE.
  - unshelve (eapply InitLib.f_sp_le_a0); CLOSE.
  - unshelve (eapply InitLib.f_sp_range); CLOSE.
  - unshelve (eapply InitLib.f_sp_align); CLOSE.
  - unshelve (eapply InitLib.f_win2); CLOSE.
  - unshelve (eapply InitLib.f_win3); CLOSE.
  - unshelve (eapply InitLib.f_win5); CLOSE.
  - unshelve (eapply InitLib.f_hwcap); CLOSE.
  - unshelve (eapply InitLib.f_win10); CLOSE.
  - unshelve (eapply InitLib.f_sp_le_a1); CLOSE.
  - unshelve (eapply InitLib.f_envp2); CLOSE.
  - unshelve (eapply InitLib.f_auxv); CLOSE.
  - unshelve (eapply InitLib.f_size8_lo); CLOSE.
  - unshelve (eapply InitLib.f_size8_hi); CLOSE.
  - unshelve (eapply InitLib.f_size9_lo); CLOSE.
  - unshelve (eapply InitLib.f_size9_hi); CLOSE.
  - unshelve (eapply InitLib.f_size10_lo); CLOSE.
  - unshelve (eapply InitLib.f_size10_hi); CLOSE.
  - unshelve (eapply InitLib.f_a0_end); CLOSE.
  - unshelve (eapply InitLib.f_a1_end); CLOSE.
  - unshelve (eapply InitLib.f_win12); CLOSE.
  - unshelve (eapply InitLib.f_align12); CLOSE.
  - unshelve (eapply InitLib.f_12_le_5); CLOSE.
  - unshelve (eapply InitLib.f_end5_12); CLOSE.
  - unshelve (eapply InitLib.f_sp_le_12); CLOSE.
  - unshelve (eapply InitLib.f_end12); CLOSE.
  - unshelve (eapply InitLib.f_12_le_10); CLOSE.
  - unshelve (eapply InitLib.f_end10_12); CLOSE.
  - unshelve (eapply InitLib.f_end2); CLOSE.
  - unshelve (eapply InitLib.f_end3); CLOSE.
  - unshelve (eapply InitLib.f_a0_end16); CLOSE.
  - unshelve (eapply InitLib.f_a0_base96); CLOSE.
  - unshelve (eapply InitLib.f_a1_end16); CLOSE.
  - unshelve (eapply InitLib.f_a1_base96); CLOSE.
Qed.

Definition stdvar (k : int) : bool :=
  match opq_get OPQ k with Some _ => false | None => match base_of DER k with Some _ => false | None => true end end.
Lemma evA_std : forall k, stdvar k = true -> ev E k = ev E0 k.
Proof.
  intros k H. cbn [ev E]. unfold evA. unfold stdvar in H. destruct (opq_get OPQ k); [discriminate|].
  destruct (base_of DER k); [discriminate| reflexivity].
Qed.
Lemma FACTS_std : forallb (fact_okb stdvar) FACTS = true. Proof. vm_compute. reflexivity. Qed.
Lemma facts_E : facts_hold E FACTS.
Proof. exact (facts_hold_agree stdvar E0 E evA_std eq_refl FACTS FACTS_std facts_E0). Qed.

Lemma ev20 : bv_unsigned (ev E 20%uint63) = 4096 * V 0%nat + 512 * V 10%nat + 2 * V 6%nat + 2147450880.
Proof.
  pose proof HB as H. unfold B in H. apply Forall_app in H as [_ H]. apply Forall_app in H as [H _]. unfold DER in H.
  inversion H as [|x l H1 _]; subst. cbn [fst snd] in H1. rewrite H1. unfold leval. cbn [fst snd lsum]. lia.
Qed.
Lemma ev64 : bv_unsigned (ev E 64%uint63) = V 44%nat.
Proof.
  pose proof HB as H. unfold B in H. apply Forall_app in H as [_ H]. apply Forall_app in H as [_ H]. unfold OPQ in H. cbn [map] in H.
  inversion H as [|x l H1 _]; subst. cbn [fst snd] in H1. rewrite H1. unfold leval, lvar. cbn [fst snd lsum]. lia.
Qed.

Lemma RSH_ok : region_ok SEGS PRIV E m 20%uint63 RSH.
Proof.
  pose proof usp_range as U. pose proof (HV 0%nat) as R0. pose proof (HV 6%nat) as R6. pose proof (HV 10%nat) as R10.
  apply (zero_region_ok SEGS V m E B HB NFS HNF PRIV 20%uint63 RSH (-1048064) 3 F_STK eq_refl F_STK_in eq_refl
           (InitLib.imap_of_bst _ _) eq_refl eq_refl eq_refl eq_refl); rewrite ?ev20.
  - lia.
  - rewrite two64_eq. lia.
  - unfold F_STK, leval. cbn [nf_a fst snd lsum]. lia.
  - unfold zlen, F_STK, leval. cbn [nf_kind nf_a nf_v fst snd lsum]. lia.
  - intros a Ha. apply noseg. unfold SEGTOP. lia.
Qed.

Lemma shmap_main : forall a, IMGSH_LO <= a < IMGSH_LO + IMGSH_LEN -> wb SEGS m a = true.
Proof.
  intros a Ha. pose proof (proj1 (Forall_forall _ _) HMF _ IMGSH_in) as W. cbn [MXm.mfact_ok MXm.zv] in W.
  destruct W as (_ & _ & W). specialize (W (a - IMGSH_LO) ltac:(lia)). replace (IMGSH_LO + (a - IMGSH_LO)) with a in W by lia.
  unfold wb. unfold AMm.wa in W. destruct (wview SEGS m (Z_to_bv 64 a)); [reflexivity | congruence].
Qed.

Lemma zro_main : forall a, IMGSH_LO <= a < IMGSH_LO + ZRO_LEN -> m (Z_to_bv 64 a) = Some (Z_to_bv 8 0) /\ wb SEGS m a = true.
Proof.
  intros a Ha. split; [| apply shmap_main; unfold ZRO_LEN, IMGSH_LEN in *; lia].
  pose proof (proj1 (Forall_forall _ _) HMF _ ZRO_in) as Zf. cbn [MXm.mfact_ok MXm.zv] in Zf.
  specialize (Zf (a - IMGSH_LO) ltac:(lia)). replace (IMGSH_LO + (a - IMGSH_LO)) with a in Zf by lia. exact Zf.
Qed.
Lemma zsh_main : forall a, ZSH_LO <= a < ZSH_HI -> m (Z_to_bv 64 a) = Some (Z_to_bv 8 0) /\ wb SEGS m a = true.
Proof.
  intros a Ha. split; [| apply shmap_main; unfold ZSH_LO, ZSH_HI, IMGSH_LO, IMGSH_LEN in *; lia].
  pose proof (proj1 (Forall_forall _ _) HMF _ ZSHF_in) as Zf. cbn [MXm.mfact_ok MXm.zv] in Zf.
  specialize (Zf (a - ZSHF_LO) ltac:(unfold ZSH_LO, ZSH_HI, ZSHF_LO, ZSHF_LEN in *; lia)). replace (ZSHF_LO + (a - ZSHF_LO)) with a in Zf by lia. exact Zf.
Qed.

Lemma zpb_main : forall a, ZPB_LO <= a < ZPB_HI -> m (Z_to_bv 64 a) = Some (Z_to_bv 8 0) /\ wb SEGS m a = true.
Proof.
  intros a Ha. split; [| apply shmap_main; unfold ZPB_LO, ZPB_HI, IMGSH_LO, IMGSH_LEN in *; lia].
  pose proof (proj1 (Forall_forall _ _) HMF _ ZPBF_in) as Zf. cbn [MXm.mfact_ok MXm.zv] in Zf.
  specialize (Zf (a - ZPBF_LO) ltac:(unfold ZPB_LO, ZPB_HI, ZPBF_LO, ZPBF_LEN in *; lia)). replace (ZPBF_LO + (a - ZPBF_LO)) with a in Zf by lia. exact Zf.
Qed.

Lemma pool_main : forall i, 0 <= i < 8 -> rb SEGS m (POOL_FL + i) = Some (Z_to_bv 8 0).
Proof.
  intros i Hi. pose proof POOL_fresh_ok as C. apply existsb_exists in C as (f & Hf & FC).
  pose proof (fact_cell_sound SEGS V m (lconst POOL_FL) 8 (lconst 0) f (proj1 (Forall_forall _ _) HNF f Hf) FC i Hi) as RB.
  rewrite !leval_lconst in RB. rewrite byte_of_zero in RB by lia. exact RB.
Qed.

Lemma gsh_main : forall a n v, In (a, n, v) GSH_TAB -> forall i, 0 <= i < n -> m (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 v).
Proof.
  intros a n v Hin i Hi. pose proof (proj1 (forallb_forall _ _) GSH_tab_ok _ Hin) as C. unfold gsh_ent_chk in C.
  apply andb_prop in C as [C QX]. apply andb_prop in C as [C QHI]. apply andb_prop in C as [C QLO]. apply andb_prop in C as [C QN].
  apply andb_prop in C as [C QV2]. apply andb_prop in C as [QC QV1].
  apply Z.leb_le in QHI, QLO, QV1. apply Z.ltb_lt in QN, QV2.
  apply existsb_exists in QX as (f & Hf & FC).
  pose proof (fact_cell_sound SEGS V m (lconst a) n (lconst v) f (proj1 (Forall_forall _ _) HNF f Hf) FC i Hi) as RB.
  rewrite !leval_lconst in RB.
  assert (BY : byte_of (Z_to_bv 64 v) i = Z_to_bv 8 v).
  { apply orb_prop in QC as [V0|N1].
    - apply Z.eqb_eq in V0. subst v. apply byte_of_zero. lia.
    - apply Z.eqb_eq in N1. assert (i = 0) by lia. subst i. unfold byte_of. rewrite Z.mul_0_r, Z.shiftr_0_r, Z_to_bv_unsigned.
      rewrite bv_wrap_small by (unfold bv_modulus; cbn [Z.of_N]; lia). reflexivity. }
  rewrite BY in RB. unfold rb in RB. destruct (m (Z_to_bv 64 (a + i))) as [b|] eqn:Em; [exact RB|].
  exfalso. unfold rom_of, memory_read in RB. rewrite Z_to_bv_unsigned in RB. unfold bv_wrap, bv_modulus in RB. cbn [Z.of_N] in RB.
  rewrite Z.mod_small in RB by lia. change (Z.of_N 1) with 1 in RB. rewrite (noseg (a + i)) in RB by (unfold SEGTOP; lia). discriminate RB.
Qed.

Lemma ssh_main : forall a, 0x7fff8000 + (usp - 8388608) / 8 <= a < 0x10007fff8000 -> wb SEGS m a = true.
Proof.
  intros a Ha. pose proof (proj1 (Forall_forall _ _) HMF _ F_MWRS_in) as W. unfold F_MWRS in W. cbn [MXm.mfact_ok MXm.zv] in W.
  pose proof usp_range as U. pose proof (HV 0%nat) as R0. pose proof (HV 6%nat) as R6. pose proof (HV 10%nat) as R10.
  assert (D : (usp - 8388608) / 8 = 4096 * V 0%nat + 512 * V 10%nat + 2 * V 6%nat - 1048576) by (symmetry; apply (Z.div_unique _ 8 _ 0); lia).
  rewrite D in Ha. destruct W as (_ & _ & W).
  specialize (W (a - (4096 * V 0%nat + 512 * V 10%nat + 2146402304)) ltac:(lia)).
  replace (4096 * V 0%nat + 512 * V 10%nat + 2146402304 + (a - (4096 * V 0%nat + 512 * V 10%nat + 2146402304))) with a in W by lia.
  unfold wb. unfold AMm.wa in W. destruct (wview SEGS m (Z_to_bv 64 a)); [reflexivity | congruence].
Qed.

Lemma zarg_main : forall s, 0x7fff8000 + (usp + 24 + 7) / 8 <= s < 0x10007fff8000 -> m (Z_to_bv 64 s) = Some (Z_to_bv 8 0) /\ wb SEGS m s = true.
Proof.
  intros s Hs. pose proof usp_range as U. pose proof (HV 0%nat) as R0. pose proof (HV 6%nat) as R6. pose proof (HV 10%nat) as R10.
  assert (D : usp / 8 = 4096 * V 0%nat + 512 * V 10%nat + 2 * V 6%nat) by (symmetry; apply (Z.div_unique _ 8 _ 0); lia).
  assert (D8 : (usp - 8388608) / 8 = usp / 8 - 1048576) by (Z.div_mod_to_equations; lia).
  assert (LB : usp / 8 <= (usp + 24 + 7) / 8) by (apply Z.div_le_mono; lia).
  split; [| apply ssh_main; lia].
  pose proof (proj1 (Forall_forall _ _) HMF _ F_MZS_in) as Zf. unfold F_MZS in Zf. cbn [MXm.mfact_ok MXm.zv] in Zf.
  specialize (Zf (s - (4096 * V 0%nat + 512 * V 10%nat + 2146402304)) ltac:(lia)).
  replace (4096 * V 0%nat + 512 * V 10%nat + 2146402304 + (s - (4096 * V 0%nat + 512 * V 10%nat + 2146402304))) with s in Zf by lia.
  exact Zf.
Qed.

Lemma facts_TW : facts_hold E FACTS_TW.
Proof.
  unfold FACTS_TW, facts_hold. repeat apply Forall_cons; try apply Forall_nil; cbn [fact_holds den].
  -
    unfold alu64, alu. rewrite (bv_add_0_r (ev E 20%uint63)) by reflexivity. rewrite (bv_add_0_r (ev E 1%uint63)) by reflexivity.
    apply bv_eq. rewrite bv_add_unsigned, bv_shiftr_unsigned, wbv_unsigned, ev20, ev1.
    change (bv_unsigned (bv_and (wbv (wp 3%uint63)) (Z_to_bv 64 63))) with 3. change (w2Z (wp 2147450880%uint63)) with 2147450880.
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    pose proof usp_range as U. pose proof (HV 0%nat) as R0. pose proof (HV 6%nat) as R6. pose proof (HV 10%nat) as R10.
    assert (D : usp / 8 = 4096 * V 0%nat + 512 * V 10%nat + 2 * V 6%nat) by (symmetry; apply (Z.div_unique _ 8 _ 0); lia).
    rewrite D. unfold bv_wrap, bv_modulus. cbn [Z.of_N]. rewrite Z.mod_small by lia. reflexivity.
  -   rewrite ev64. change (w2Z (wp 1%uint63)) with 1. change (w2Z (wp 4194303%uint63)) with 4194303. exact Ptid.
Qed.

Variable ms : machine_state.
Hypothesis Hms :
  ms = ASTm.MS (AFm.mkR (Z_to_bv 64 MEm.ARA) (Z_to_bv 64 (usp - 48)) (Z_to_bv 64 MEm.AGP) (Z_to_bv 64 MEm.ATP)
                 (Z_to_bv 64 (V 856%nat)) (Z_to_bv 64 (V 857%nat)) (Z_to_bv 64 (V 858%nat))
                 (Z_to_bv 64 (usp + 8)) (Z_to_bv 64 argc) (Z_to_bv 64 argc) (Z_to_bv 64 (usp + 8))
                 (Z_to_bv 64 (usp + 8 * argc + 16)) (Z_to_bv 64 0x6000000000000000)
                 (Z_to_bv 64 (V 859%nat)) (Z_to_bv 64 (V 860%nat)) (Z_to_bv 64 (V 861%nat)) (Z_to_bv 64 (V 862%nat))
                 (Z_to_bv 64 MEm.AMAIN) (Z_to_bv 64 (usp + 8 * argc + 16))
                 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                 (Z_to_bv 64 (V 863%nat)) (Z_to_bv 64 (V 864%nat)) (Z_to_bv 64 (V 865%nat)) (Z_to_bv 64 (V 866%nat)))
            bvmap_empty (Z_to_bv 64 MEm.AMAIN) (Z_to_bv 32 0) None m (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.seg_rom SEGS).

Lemma argc2 : argc = 2. Proof. unfold argc. rewrite Hargc2. reflexivity. Qed.

Local Ltac REG := eapply (word_is_sv V E B HB); [vm_compute; reflexivity | unfold leval; cbn [fst snd lsum]; f_equal; pose proof Pusp; pose proof argc2; lia].

Local Ltac REGN k :=
  eapply eq_trans; [apply MXm.reg_get_mkR with (n := k); lia | cbn [nth]; REG].

Lemma so_regsA : forall r,
  rget (Core (ms_regs ms) (ms_fregs ms) (ms_pc_val ms) (ms_fcsr ms) (ms_resv ms)) (reg_of_r5 r) = den E (rf_get RFA r).
Proof.
  intros r. rewrite Hms. cbn [ASTm.MS ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv]. unfold rget. cbn [c_regs].
  destruct r; [reflexivity | ..]; (change (is_x0 (reg_of_r5 _)) with false; cbv iota).
  - REGN 1%nat. - REGN 2%nat. - REGN 3%nat. - REGN 4%nat. - REGN 5%nat. - REGN 6%nat. - REGN 7%nat. - REGN 8%nat.
  - REGN 9%nat. - REGN 10%nat. - REGN 11%nat. - REGN 12%nat. - REGN 13%nat. - REGN 14%nat. - REGN 15%nat. - REGN 16%nat.
  - REGN 17%nat. - REGN 18%nat. - REGN 19%nat. - REGN 20%nat. - REGN 21%nat. - REGN 22%nat. - REGN 23%nat. - REGN 24%nat.
  - REGN 25%nat. - REGN 26%nat. - REGN 27%nat. - REGN 28%nat. - REGN 29%nat. - REGN 30%nat. - REGN 31%nat.
Qed.

Lemma REGS_bst : IMap.bst REGS. Proof. unfold REGS. apply InitLib.imap_of_bst. Qed.

Lemma regs_cases : forall k r, IMap.find k REGS = Some r ->
  (k = 0%uint63 /\ r = R0) \/ (k = 1%uint63 /\ r = R1) \/ (k = 2%uint63 /\ r = InitLib.R2T) \/ (k = 3%uint63 /\ r = R3)
  \/ (k = 5%uint63 /\ r = InitLib.R5T) \/ (k = 10%uint63 /\ r = InitLib.R10T) \/ (k = 12%uint63 /\ r = InitLib.R12T)
  \/ (k = 20%uint63 /\ r = RSH).
Proof.
  intros k r H. apply (InitLib.find_in_elements _ k r REGS REGS_bst) in H. rewrite REGS_elements in H.
  assert (EL : REGS_L = [(0%uint63, R0); (1%uint63, R1); (2%uint63, InitLib.R2T); (3%uint63, R3); (5%uint63, InitLib.R5T);
                         (10%uint63, InitLib.R10T); (12%uint63, InitLib.R12T); (20%uint63, RSH)]) by (vm_compute; reflexivity).
  rewrite EL in H. cbn [In] in H. intuition congruence.
Qed.

Lemma based_apart : forall k r, IMap.find k REGS = Some r -> k <> 0%uint63 -> k <> 1%uint63 ->
  rg_w r = false /\ (usp + 32 <= bv_unsigned (ev E k) + loZ r \/ bv_unsigned (ev E k) + hiZ E r <= usp - 8388608).
Proof.
  intros k r H K0 K1. pose proof envc_range as EC. pose proof sstructZ as SS. pose proof argc2 as A2. pose proof usp_range as U.
  destruct (regs_cases k r H) as [[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]]]]]; try congruence; (split; [reflexivity|]).
  - left. change (ev E 2%uint63) with (ev E0 2%uint63). unfold E0. rewrite (InitLib.ev0_2 PH sp argv envp uid hwcap draw xb0 Hva Hve Hsp Hfit).
    rewrite (InitLib.loZ_0 InitLib.R2T eq_refl). unfold SI.envp_off, SI.argcZ, SI.nargc, SI.SP. fold usp argc. lia.
  - left. rewrite ev3. change (loZ R3) with 0. lia.
  - left. change (ev E 5%uint63) with (ev E0 5%uint63). unfold E0. rewrite (InitLib.ev0_5 PH sp argv envp uid hwcap draw xb0 Hfit).
    rewrite (InitLib.loZ_0 InitLib.R5T eq_refl). unfold SI.SP. fold usp. lia.
  - left. change (ev E 10%uint63) with (ev E0 10%uint63). unfold E0. rewrite (InitLib.ev0_10 PH sp argv envp uid hwcap draw xb0 Hva Hsp Hfit).
    rewrite (InitLib.loZ_0 InitLib.R10T eq_refl). unfold SI.SP. fold usp. lia.
  - left. change (ev E 12%uint63) with (ev E0 12%uint63). unfold E0. rewrite (InitLib.ev0_12 PH sp argv envp uid hwcap draw xb0 Hfit).
    rewrite (InitLib.loZ_0 InitLib.R12T eq_refl). unfold SI.SP. fold usp. lia.
  - right. rewrite ev20. change (hiZ E RSH) with 3. pose proof (HV 0%nat). pose proof (HV 6%nat). pose proof (HV 10%nat). pose proof Pusp. lia.
Qed.

Definition HULL (a : Z) : Prop :=
  (exists seg, find_segment SEGS a 1 = Some seg)
  \/ (usp - 8384512 <= a < usp + Z.of_nat (length (build_stack_bytes PH sp argv envp uid hwcap draw)))
  \/ (usp / 8 + 2147450880 - 1048064 <= a < usp / 8 + 2147450880 + 3).

Definition BHULL (a : Z) : Prop :=
  (usp - 8384512 <= a < usp + Z.of_nat (length (build_stack_bytes PH sp argv envp uid hwcap draw)))
  \/ (usp / 8 + 2147450880 - 1048064 <= a < usp / 8 + 2147450880 + 3).
Lemma stack_top_47 : usp + Z.of_nat (length (build_stack_bytes PH sp argv envp uid hwcap draw)) <= 2 ^ 47.
Proof. pose proof (SI.BSB_top PH sp argv envp uid hwcap draw Hfit) as T. unfold SI.SP, SI.BSB in T. fold usp in T. exact T. Qed.

Lemma based_hull : forall a, in_based E REGS a -> BHULL a.
Proof.
  intros a B0. destruct B0 as (k & r & Hk & K & Ha).
  pose proof envc_range as EC. pose proof sstructZ as SS. pose proof argc2 as A2. pose proof usp_range as U. pose proof strZ as SZ.
  pose proof (InitLib.len_BSB PH sp argv envp uid hwcap draw) as HL. unfold SI.BSB in HL.
  pose proof (InitLib.total_ge_a0 PH sp argv envp uid hwcap draw Hva) as TA.
  assert (TN : 0 <= Z.of_nat (SI.total_nat argv) /\ 0 <= Z.of_nat (SI.total_nat envp) /\ 0 <= Z.of_nat (SI.pad argv envp)) by lia.
  destruct (regs_cases k r Hk) as [[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]]]]]; try discriminate K.
  -   left. rewrite ev1 in Ha. change (loZ R1) with (-8384512) in Ha. change (hiZ E R1) with 24 in Ha. lia.
  -   left. change (ev E 2%uint63) with (ev E0 2%uint63) in Ha. unfold E0 in Ha.
    rewrite (InitLib.ev0_2 PH sp argv envp uid hwcap draw xb0 Hva Hve Hsp Hfit) in Ha. rewrite (InitLib.loZ_0 InitLib.R2T eq_refl) in Ha.
    change (hiZ E InitLib.R2T) with (hiZ E0 InitLib.R2T) in Ha. unfold E0 in Ha. rewrite (InitLib.hiZ_R2 PH sp argv envp uid hwcap draw xb0 Hve) in Ha.
    unfold SI.envp_off, SI.argcZ, SI.envcZ, SI.nargc, SI.nenvc, SI.SP in Ha. fold usp argc envc in Ha. lia.
  -   left. rewrite ev3 in Ha. change (loZ R3) with 0 in Ha. change (hiZ E R3) with 160 in Ha. lia.
  -   left. change (ev E 5%uint63) with (ev E0 5%uint63) in Ha. unfold E0 in Ha.
    rewrite (InitLib.ev0_5 PH sp argv envp uid hwcap draw xb0 Hfit) in Ha. rewrite (InitLib.loZ_0 InitLib.R5T eq_refl) in Ha.
    change (hiZ E InitLib.R5T) with (hiZ E0 InitLib.R5T) in Ha. unfold E0 in Ha. rewrite (InitLib.hiZ_R5 PH sp argv envp uid hwcap draw xb0 Hva) in Ha.
    unfold SI.SP in Ha. fold usp in Ha. lia.
  -   left. change (ev E 10%uint63) with (ev E0 10%uint63) in Ha. unfold E0 in Ha.
    rewrite (InitLib.ev0_10 PH sp argv envp uid hwcap draw xb0 Hva Hsp Hfit) in Ha. rewrite (InitLib.loZ_0 InitLib.R10T eq_refl) in Ha.
    change (hiZ E InitLib.R10T) with (hiZ E0 InitLib.R10T) in Ha. unfold E0 in Ha.
    rewrite (InitLib.hiZ_R10 SEGS PCN PH sp argv envp uid hwcap draw xb0 Hva Hfit Hargc2) in Ha.
    pose proof (InitLib.total2 SEGS PCN PH sp argv envp uid hwcap draw Hva Hfit Hargc2) as T2. unfold SI.SP in Ha. fold usp in Ha. lia.
  -   left. change (ev E 12%uint63) with (ev E0 12%uint63) in Ha. unfold E0 in Ha.
    rewrite (InitLib.ev0_12 PH sp argv envp uid hwcap draw xb0 Hfit) in Ha. rewrite (InitLib.loZ_0 InitLib.R12T eq_refl) in Ha.
    change (hiZ E InitLib.R12T) with (hiZ E0 InitLib.R12T) in Ha. unfold E0 in Ha. rewrite (InitLib.hiZ_R12 PH sp argv envp uid hwcap draw xb0 Hsp Hfit) in Ha.
    rewrite (InitLib.strarea_len PH sp argv envp uid hwcap draw) in Ha. unfold SI.SP in Ha. fold usp in Ha. lia.
  -   right. rewrite ev20 in Ha. change (loZ RSH) with (-1048064) in Ha. change (hiZ E RSH) with 3 in Ha.
    pose proof (HV 0%nat). pose proof (HV 6%nat). pose proof (HV 10%nat).
    assert (D : usp / 8 = 4096 * V 0%nat + 512 * V 10%nat + 2 * V 6%nat) by (symmetry; apply (Z.div_unique _ 8 _ 0); lia).
    rewrite D. lia.
Qed.

Lemma fx_acc_hull : forall a, fx_acc SEGS E REGS a -> HULL a.
Proof. intros a [B0|S]; [right; exact (based_hull a B0)| left; exact S]. Qed.

Definition ROOT_with (os : list opinst) : sstate := SS MAINPC RFA FFA RNone REGS (FACTS ++ FACTS_TW) os PRIV 128%uint63.
Theorem main_st_ok_ops : forall (OPS : optable) (mo : Model) (os : list opinst),
  op_minv OPS mo -> ops_hold OPS E os m mo -> ops_apart SEGS OPS E os REGS PRIV ->
  (forall a, fx_acc SEGS E REGS a -> op_cov OPS (insts E os) a) ->
  st_ok SEGS OPS E (ROOT_with os) ms mo.
Proof.
  intros OPS mo os Hmi Hops Hapart Hcov. split; cbn [ROOT_with s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv].
  - rewrite Hms. reflexivity.
  - reflexivity.
  - exact so_regsA.
  - intros r. rewrite Hms. destruct r; reflexivity.
  - rewrite Hms. reflexivity.
  - rewrite Hms. reflexivity.
  - rewrite Hms. cbn. reflexivity.
  - rewrite Hms. reflexivity.
  - exact ev0A.
  - exact REGS_bst.
  - intros k r Hk. rewrite Hms. cbn [ASTm.MS ms_mem].
    destruct (regs_cases k r Hk) as [[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]]]]];
      [exact R0_ok | exact R1_ok | exact R2_okA | exact R3_ok | exact R5_okA | exact R10_okA | exact R12_okA | exact RSH_ok].
  - intros k1 r1 k2 r2 H1 H2 Hne Hk1 Hk2 Hw a [Ha1 Ha2].
    assert (S1 : forall r, IMap.find 1%uint63 REGS = Some r -> r = R1).
    { intros r Hr. destruct (regs_cases _ r Hr) as [[X _]|[[_ ->]|[[X _]|[[X _]|[[X _]|[[X _]|[[X _]|[X _]]]]]]]]; try discriminate X. reflexivity. }
    assert (K0 : forall k, PrimInt63.eqb k 0%uint63 = false -> k <> 0%uint63) by (intros k Hk ->; discriminate Hk).
    destruct (PrimInt63.eqb k1 1%uint63) eqn:E1; [apply Uint63.eqb_correct in E1; subst k1| apply Uint63.eqb_false_spec in E1; rename E1 into N1];
    (destruct (PrimInt63.eqb k2 1%uint63) eqn:E2; [apply Uint63.eqb_correct in E2; subst k2| apply Uint63.eqb_false_spec in E2; rename E2 into N2]).
    + apply Hne. reflexivity.
    + rewrite (S1 r1 H1) in Ha1. destruct (based_apart k2 r2 H2 (K0 _ Hk2) N2) as [_ L]. rewrite ev1 in Ha1. change (hiZ E R1) with 24 in Ha1.
      change (loZ R1) with (-8384512) in Ha1. lia.
    + rewrite (S1 r2 H2) in Ha2. destruct (based_apart k1 r1 H1 (K0 _ Hk1) N1) as [_ L]. rewrite ev1 in Ha2. change (hiZ E R1) with 24 in Ha2.
      change (loZ R1) with (-8384512) in Ha2. lia.
    + destruct (based_apart k1 r1 H1 (K0 _ Hk1) N1) as [W1 _]. destruct (based_apart k2 r2 H2 (K0 _ Hk2) N2) as [W2 _].
      destruct Hw as [Hw|Hw]; congruence.
  - intros r g gr c Hr Hg Hc i Hi.
    assert (r = R0). { destruct (regs_cases _ r Hr) as [[_ ->]|[[X _]|[[X _]|[[X _]|[[X _]|[[X _]|[[X _]|[X _]]]]]]]]; try discriminate X. reflexivity. }
    subst r. exact (cells_public0 SEGS B NFS PRIV R0 R0_bst R0_cells_ok g gr c Hg Hc i Hi).
  - unfold facts_hold. apply Forall_app. split; [exact facts_E| exact facts_TW].
  - rewrite Hms. cbn [ASTm.MS ms_mem]. exact Hops.
  - exact Hapart.
  - exact Hmi.
  - exact Hcov.
  - rewrite Hms. cbn [ASTm.MS ms_mem]. intros a b Hab seg Hseg. pose proof (Hminv a b Hab) as R. unfold AMm.ro_addr in R. rewrite Hseg in R.
    destruct (seg_writable seg); [reflexivity| discriminate R].
Qed.

Theorem main_st_ok : forall (OPS : optable) (mo : Model),
  op_minv OPS mo ->
  (forall a, fx_acc SEGS E REGS a -> op_cov OPS [] a) ->
  st_ok SEGS OPS E ROOT ms mo.
Proof. intros OPS mo Hmi Hcov. exact (main_st_ok_ops OPS mo [] Hmi (Forall_nil _) (Forall_nil _) Hcov). Qed.

End Main.

Theorem amain_st_ok : forall (xb0 : int -> list byte) (en : ExecEntry) (inp : ProcInput) (ms : machine_state) (mo : Model),
  valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_sp (en_sp en) ->
  entry_stack_fits (en_sp en) (in_argv inp) (in_envp inp) -> valid_hwcap (in_hwcap inp) ->
  length (in_argv inp) = 2%nat ->
  MEm.amain_at en inp ms mo ->
  exists E : env,
    eb E = eb (InitLib.E0 (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) xb0) /\
    (forall a, fx_acc SEGS E REGS a -> HULL (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) a) /\
    forall OPS : optable, op_minv OPS mo -> (forall a, fx_acc SEGS E REGS a -> op_cov OPS [] a) -> st_ok SEGS OPS E ROOT ms mo.
Proof.
  intros xb0 en inp ms mo Hva Hve Hsp Hfit Hhw Hargc2 HM.
  destruct HM as (w & V & m & Hms & HV & (P0 & P6 & P10 & Pusp & P1 & P2 & P3 & P7 & P4 & P5 & P8 & P9) & HMF & HPF & Hminv & Hstk & Hhid & _ & _).
  assert (HMF1 : Forall (MXm.mfact_ok SEGS V m) MFm.asan_mem_facts) by (exact (proj1 (proj1 (Forall_app _ _ _) HMF))).
  assert (Ptid : 1 <= V 44%nat <= 4194303).
  { apply (proj1 (Forall_forall _ _) (proj1 (proj1 (Forall_app _ _ _) HPF)) (MXm.PVar 44 1 4194303)).
    unfold MFm.asan_pure_facts. repeat first [left; reflexivity | right]. }
  exists (E xb0 (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) V m). split; [reflexivity|]. split.
  { intros a Ha. eapply (fx_acc_hull xb0 (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en)) with (V := V) (m := m); eassumption. }
  intros OPS Hmi Hcov.
  eapply (main_st_ok xb0 (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) Hva Hve Hsp Hfit Hhw Hargc2 V m); try eassumption.
  intros a Ha. etransitivity; [apply (Hhid a)| reflexivity].
  unfold MEm.hidden_arg. cbv zeta. rewrite <- P4. exact Ha.
Qed.

Theorem amain_st_ok_ops : forall (xb0 : int -> list byte) (en : ExecEntry) (inp : ProcInput) (ms : machine_state) (mo : Model),
  valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_sp (en_sp en) ->
  entry_stack_fits (en_sp en) (in_argv inp) (in_envp inp) -> valid_hwcap (in_hwcap inp) ->
  length (in_argv inp) = 2%nat ->
  MEm.amain_at en inp ms mo ->
  exists E : env,
    eb E = eb (InitLib.E0 (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) xb0) /\
    (forall a, fx_acc SEGS E REGS a -> HULL (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) a) /\
    (forall a, in_based E REGS a -> (bv_unsigned (en_sp en) - 8384512 <= a < 2 ^ 47)
                                   \/ (bv_unsigned (en_sp en) / 8 + 2147450880 - 1048064 <= a < bv_unsigned (en_sp en) / 8 + 2147450880 + 3)) /\
    bv_unsigned (ev E 1%uint63) = bv_unsigned (en_sp en) /\

    (forall a, IMGSH_LO <= a < IMGSH_LO + IMGSH_LEN -> wb SEGS (ms_mem ms) a = true) /\
    (forall a, IMGSH_LO <= a < IMGSH_LO + ZRO_LEN -> ms_mem ms (Z_to_bv 64 a) = Some (Z_to_bv 8 0) /\ wb SEGS (ms_mem ms) a = true) /\
    (forall a, ZSH_LO <= a < ZSH_HI -> ms_mem ms (Z_to_bv 64 a) = Some (Z_to_bv 8 0) /\ wb SEGS (ms_mem ms) a = true) /\
    (forall a, ZPB_LO <= a < ZPB_HI -> ms_mem ms (Z_to_bv 64 a) = Some (Z_to_bv 8 0) /\ wb SEGS (ms_mem ms) a = true) /\
    (forall a n v, In (a, n, v) GSH_TAB -> forall i, 0 <= i < n -> ms_mem ms (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 v)) /\
    (forall i, 0 <= i < 8 -> rb SEGS (ms_mem ms) (POOL_FL + i) = Some (Z_to_bv 8 0)) /\
    (forall a, 0x7fff8000 + (bv_unsigned (en_sp en) - 8388608) / 8 <= a < 0x10007fff8000 -> wb SEGS (ms_mem ms) a = true) /\
    (forall a, 0x7fff8000 + (bv_unsigned (en_sp en) + 24 + 7) / 8 <= a < 0x10007fff8000 -> ms_mem ms (Z_to_bv 64 a) = Some (Z_to_bv 8 0) /\ wb SEGS (ms_mem ms) a = true) /\
    forall (OPS : optable) (os : list opinst), op_minv OPS mo -> ops_hold OPS E os (ms_mem ms) mo -> ops_apart SEGS OPS E os REGS PRIV ->
      (forall a, fx_acc SEGS E REGS a -> op_cov OPS (insts E os) a) -> st_ok SEGS OPS E (ROOT_with os) ms mo.
Proof.
  intros xb0 en inp ms mo Hva Hve Hsp Hfit Hhw Hargc2 HM.
  destruct HM as (w & V & m & Hms & HV & (P0 & P6 & P10 & Pusp & P1 & P2 & P3 & P7 & P4 & P5 & P8 & P9) & HMF & HPF & Hminv & Hstk & Hhid & _ & _).
  assert (HMF1 : Forall (MXm.mfact_ok SEGS V m) MFm.asan_mem_facts) by (exact (proj1 (proj1 (Forall_app _ _ _) HMF))).
  assert (Ptid : 1 <= V 44%nat <= 4194303).
  { apply (proj1 (Forall_forall _ _) (proj1 (proj1 (Forall_app _ _ _) HPF)) (MXm.PVar 44 1 4194303)).
    unfold MFm.asan_pure_facts. repeat first [left; reflexivity | right]. }
  exists (E xb0 (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) V m). split; [reflexivity|]. split.
  { intros a Ha. eapply (fx_acc_hull xb0 (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en)) with (V := V) (m := m); eassumption. }
  split.
  { intros a Ha.
    pose proof (stack_top_47 (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) Hfit) as T47.
    assert (BH : BHULL (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) a).
    { eapply (based_hull xb0 (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en)) with (V := V) (m := m); eassumption. }
    destruct BH as [BH|BH]; [left; lia| right; exact BH]. }
  split; [apply ev1|].
  assert (EM : ms_mem ms = m) by (rewrite Hms; reflexivity).
  rewrite EM.
  split; [exact (shmap_main (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) Hargc2 V m HMF1)|].
  split; [exact (zro_main (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) Hargc2 V m HMF1)|].
  split; [exact (zsh_main (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) Hargc2 V m HMF1)|].
  split; [exact (zpb_main (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) Hargc2 V m HMF1)|].
  split; [intros a0 n0 v0 Hin0 i0 Hi0; exact (gsh_main (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) Hargc2 V m P1 HMF1 a0 n0 v0 Hin0 i0 Hi0)|].
  split; [exact (pool_main (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) Hargc2 V m P1 HMF1)|].
  split; [exact (ssh_main xb0 (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) Hva Hve Hsp Hfit Hargc2 V m HV Pusp HMF1)|].
  split; [exact (zarg_main xb0 (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) Hva Hve Hsp Hfit Hargc2 V m HV Pusp HMF1)|].
  intros OPS os Hmi Hops Hapart Hcov.
  eapply (main_st_ok_ops xb0 (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) Hva Hve Hsp Hfit Hhw Hargc2 V m); try eassumption.
  intros a Ha. etransitivity; [apply (Hhid a)| reflexivity].
  unfold MEm.hidden_arg. cbv zeta. rewrite <- P4. exact Ha.
Qed.

End InitAsan2.
