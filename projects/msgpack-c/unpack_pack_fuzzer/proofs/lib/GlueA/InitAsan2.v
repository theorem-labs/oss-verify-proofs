(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's whole ProcInput and mmap base; Linux's stack block, the variables' forms per CONFIG_RSEQ value; the main entry's remade facts; region 1 from the launch's window below sp; the root per region 3, the launch's auxv at the run's CONFIG_RSEQ value proved from the main entry's facts (its words, AT_EGID's word as AT_GID's, its readable range) or the region both values imply, each the ASan images' (AT_PHNUM's value 11), in place of the 20-word one, with the auxv's end bound at its size; the stack's shadow view at its moved start; the string area's end alignment fact; launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef)). *)
From Stdlib Require Import ZArith NArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics StackLayout Fs State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Mem Cells Step Frame PropExec MState.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require MainExport MainFactsAsan MainEntry.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AImg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Notation.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Regen Auxv.
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

(* the main entry's reach: an image byte, the stack window below sp up to the stack VMA's end, or the stack's shadow *)
Definition HULL (sp : word) (draw : EntryDraw) (a : Z) : Prop :=
  (exists seg, find_segment SEGS a 1 = Some seg)
  \/ (bv_unsigned sp - 6144513 <= a < bv_unsigned (SI.TOP draw))
  \/ (bv_unsigned sp / 8 + 2147450880 - 1048064 <= a < bv_unsigned sp / 8 + 2147450880 + 3).

Definition BHULL (sp : word) (draw : EntryDraw) (a : Z) : Prop :=
  (bv_unsigned sp - 6144513 <= a < bv_unsigned (SI.TOP draw))
  \/ (bv_unsigned sp / 8 + 2147450880 - 1048064 <= a < bv_unsigned sp / 8 + 2147450880 + 3).

Section Main.
Variable xb0 : int -> list byte.
Variables (sp brk0 mbase : word) (inp : ProcInput) (draw : EntryDraw).
Notation argv := (in_argv inp).
Notation envp := (in_envp inp).
Notation uid := (in_uid inp).
Notation hwcap := (in_hwcap inp).
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hlaunch : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase draw) inp.
Hypothesis Hhw : valid_hwcap hwcap.
Hypothesis Hvl : valid_launch inp.
Hypothesis Hargc2 : length argv = 2%nat.
Let usp : Z := bv_unsigned sp.
Let argc : Z := Z.of_nat (length argv).
Let envc : Z := Z.of_nat (length envp).
Let RZ : Z := MEm.RZ_of inp.

Variables (V : nat -> Z) (m : word -> option byte) (w : bool).
Hypothesis HV : forall n, 0 <= V n < 2 ^ 64.
Hypothesis Pusp : 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat = usp.
Hypothesis Pargc : V 1%nat = argc.
Hypothesis Penvc : V 2%nat = envc.
Hypothesis Pa0 : V 3%nat = Z.of_nat (length (nth 0 argv [])).
(* LPS 727298f3: [V 4] is the pad between the AT_RANDOM bytes and argv[0], [8 * V 11] the gap below the
   AT_RANDOM bytes *)
Hypothesis Ppad : V 4%nat = Z.of_nat (SI.pad sp mbase inp draw).
Hypothesis Pgap : 8 * V 11%nat = Z.of_nat (SI.gap inp).
Hypothesis Puid : V 8%nat = bv_unsigned uid.
Hypothesis Phw : V 9%nat = bv_unsigned hwcap.
Hypothesis Ptid : 1 <= V 44%nat <= 4194303.
Hypothesis HMF : Forall (MXm.mfact_ok SEGS V m) (MEm.amf RZ w).
Hypothesis Hminv : AMm.mem_inv SEGS m.

Definition E0 : env := InitLib.E0 PCN PH sp mbase inp draw xb0.
Local Notation mem0 := (SI.mem0 SEGS PCN PH sp mbase inp draw).

Local Ltac CLOSE := first [eassumption | exact PH | exact SEGS | exact PCN | exact SEGTOP | exact segs_top | exact segtop_low | exact brk0 | exact mbase].

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
Lemma a1_nth : nth 1 argv [] = hd [] (tl argv). Proof. destruct argv as [|x [|y r]]; reflexivity. Qed.
Lemma argc2 : argc = 2. Proof. unfold argc. rewrite Hargc2. reflexivity. Qed.

(* the start state's values InitLib states, at this section's launch *)
Lemma usp_range : 0x7fff80000000 <= usp <= 0x7fffffffff28.
Proof.
  assert (F : fact_holds E0 (FRange 1%uint63 (wp 140735340871680%uint63) (wp 140737488355112%uint63)))
    by (unfold E0; unshelve (eapply InitLib.f_sp_range); CLOSE).
  cbn [fact_holds] in F. unfold E0 in F. rewrite InitLib.ev0_1 in F. fold usp in F. exact F.
Qed.
Lemma ev2E : bv_unsigned (ev E0 2%uint63) = SI.SP sp + SI.envp_off inp.
Proof. unfold E0. unshelve (eapply InitLib.ev0_2); CLOSE. Qed.
Lemma ev3E : bv_unsigned (ev E0 3%uint63) = SI.SP sp + SI.auxv_off inp.
Proof. unfold E0. unshelve (eapply InitLib.ev0_3); CLOSE. Qed.
Lemma ev5E : bv_unsigned (ev E0 5%uint63) = SI.SP sp + Z.of_nat (SI.HEAD sp mbase inp + SI.pad sp mbase inp draw).
Proof. unfold E0. unshelve (eapply InitLib.ev0_5); CLOSE. Qed.
Lemma ev6E : bv_unsigned (ev E0 6%uint63) = SI.SP sp + Z.of_nat (SI.HEAD sp mbase inp - 16).
Proof. unfold E0. unshelve (eapply InitLib.ev0_6); CLOSE. Qed.
Lemma ev10E : bv_unsigned (ev E0 10%uint63) = SI.SP sp + Z.of_nat (SI.HEAD sp mbase inp + SI.pad sp mbase inp draw) + Z.of_nat (length (hd [] argv)) + 1.
Proof. unfold E0. unshelve (eapply InitLib.ev0_10); CLOSE. Qed.
Lemma ev12E : bv_unsigned (ev E0 12%uint63) = SI.SP sp + Z.of_nat (SI.HEAD sp mbase inp + SI.pad sp mbase inp draw).
Proof. unfold E0. unshelve (eapply InitLib.ev0_12); CLOSE. Qed.
Lemma topE : SI.SP sp + Z.of_nat (SI.HEAD sp mbase inp + SI.pad sp mbase inp draw) = bv_unsigned (SI.TOP draw) - 8 - Z.of_nat (SI.LSB inp).
Proof. unshelve (eapply InitLib.sstruct_eq_top); CLOSE. Qed.
Lemma tot_a0 : Z.of_nat (length (hd [] argv)) + 1 <= Z.of_nat (SI.total_nat argv).
Proof. unshelve (eapply InitLib.total_ge_a0); CLOSE. Qed.
Lemma tot2 : Z.of_nat (SI.total_nat argv) = Z.of_nat (length (hd [] argv)) + 1 + Z.of_nat (length (hd [] (tl argv))) + 1.
Proof. unshelve (eapply InitLib.total2); CLOSE. Qed.
Lemma top_hi : bv_unsigned (SI.TOP draw) <= 0x800000000000.
Proof. exact (SI.top_hi sp brk0 mbase inp draw Hlaunch). Qed.
Lemma LSBZ : Z.of_nat (SI.LSB inp) = Z.of_nat (SI.total_nat argv) + Z.of_nat (SI.total_nat envp) + Z.of_nat (length (in_execfn inp)) + 1.
Proof. exact (SI.LSB_eq inp). Qed.
(* the block's head, sp to the AT_RANDOM bytes' end *)
(* the auxv's size, 432 bytes or 464 with CONFIG_RSEQ *)
Lemma auxszE : Z.of_nat (auxv_size (la_rseq (SI.LA sp mbase inp))) = 432 + 32 * RZ.
Proof. rewrite (SI.LA_rseq sp mbase inp). unfold RZ, MEm.RZ_of. destruct (kb_rseq (in_kernel inp)); reflexivity. Qed.
Lemma HEADZ : Z.of_nat (SI.HEAD sp mbase inp) = 8 * argc + 8 * envc + 40 + (432 + 32 * RZ) + 8 * V 11%nat.
Proof. rewrite (SI.HEAD_eq sp mbase inp), Pgap, auxszE. unfold SI.nargc, SI.nenvc. fold argc envc. lia. Qed.
Lemma RZ_range : RZ = 0 \/ RZ = 1.
Proof. unfold RZ, MEm.RZ_of. destruct (kb_rseq (in_kernel inp)); [right|left]; reflexivity. Qed.
(* argv[0] where the main entry states it (MainEntry.STR0_of) *)
Lemma STR0E : MEm.STR0_of (mkEntry sp brk0 mbase draw) inp = bv_unsigned (ev E0 5%uint63).
Proof.
  rewrite ev5E. unfold MEm.STR0_of, MEm.Wpad, SI.SP, SI.HEAD, SI.pad, SI.TOP. cbn [en_sp en_draw].
  rewrite (SI.LA_rseq sp mbase inp), Nat2Z.inj_add. lia.
Qed.

Lemma OPQ_first : forallb (fun kn => match opq_get OPQ (fst kn) with Some n => Nat.eqb n (snd kn) | None => false end) OPQ = true.
Proof. vm_compute. reflexivity. Qed.

Lemma HB : Forall (fun kb => bv_unsigned (ev E (fst kb)) = leval V (snd kb)) (B RZ).
Proof.
  pose proof usp_range as U. pose proof HEADZ as HZ. pose proof argc2 as A2.
  pose proof ev2E as E2. pose proof ev3E as E3. pose proof ev5E as E5. pose proof ev6E as E6. pose proof ev10E as E10.
  unfold SI.envp_off, SI.auxv_off, SI.argcZ, SI.envcZ, SI.nargc, SI.nenvc, SI.SP in E2, E3. fold usp argc envc in E2, E3.
  unfold SI.SP in E5, E6, E10. fold usp in E5, E6, E10. rewrite Nat2Z.inj_add in E5, E10.
  assert (HG : 16 <= Z.of_nat (SI.HEAD sp mbase inp)) by (pose proof RZ_range; lia).
  rewrite Nat2Z.inj_sub in E6 by lia.
  rewrite <- a0_nth, <- Pa0 in E10. rewrite <- Ppad in E5, E10.
  unfold B. apply Forall_app. split; [|apply Forall_app; split; [|apply Forall_app; split]].
  - unfold BSTDC. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd ev E]; unfold leval; cbn [fst snd lsum].
    + change (evA 0%uint63) with (ev E0 0%uint63). unfold E0. rewrite InitLib.ev0_0. reflexivity.
    + change (evA 1%uint63) with (ev E0 1%uint63). unfold E0. rewrite InitLib.ev0_1. fold usp. lia.
    + change (evA 2%uint63) with (ev E0 2%uint63). rewrite E2. lia.
    + change (evA 3%uint63) with (ev E0 3%uint63). rewrite E3. lia.
    + change (evA 7%uint63) with (ev E0 7%uint63). unfold E0. rewrite InitLib.ev0_7. lia.
    + change (evA 8%uint63) with (ev E0 8%uint63). unfold E0. rewrite InitLib.ev0_8. lia.
  -
    pose proof (HV 0%nat) as R0. pose proof (HV 6%nat) as R6. pose proof (HV 10%nat) as R10.
    unfold DER. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd ev E];
      match goal with |- bv_unsigned (evA ?k) = leval V ?l => change (evA k) with (Z_to_bv 64 (leval V l)) end;
      rewrite ubv; first [reflexivity | unfold leval; cbn [fst snd lsum]; lia].
  - apply Forall_forall. intros kb Hkb. apply in_map_iff in Hkb as (kn & <- & Hkn). cbn [fst snd ev E].
    pose proof (proj1 (forallb_forall _ _) OPQ_first kn Hkn) as F. cbv beta in F. unfold evA.
    destruct (opq_get OPQ (fst kn)) as [n|]; [|discriminate]. apply Nat.eqb_eq in F. subst n.
    rewrite (ubv _ (HV _)). rewrite leval_lvar. reflexivity.
  - unfold BSTD. destruct (Z.eqb_spec RZ 1) as [R1'|R1']; [unfold BSTD1| unfold BSTD0; assert (RZ = 0) by (pose proof RZ_range; lia)];
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd ev E]; unfold leval; cbn [fst snd lsum].
    + change (evA 5%uint63) with (ev E0 5%uint63). rewrite E5. lia.
    + change (evA 6%uint63) with (ev E0 6%uint63). rewrite E6. lia.
    + change (evA 10%uint63) with (ev E0 10%uint63). rewrite E10. lia.
    + change (evA 5%uint63) with (ev E0 5%uint63). rewrite E5. lia.
    + change (evA 6%uint63) with (ev E0 6%uint63). rewrite E6. lia.
    + change (evA 10%uint63) with (ev E0 10%uint63). rewrite E10. lia.
Qed.

Lemma HNF : Forall (nfact_ok SEGS V m) (NFS RZ w).
Proof.
  rewrite NFS_eq. apply Forall_forall. intros f Hf. apply in_map_iff in Hf as (f0 & <- & Hf0).
  apply (norm_fact_sound SEGS V m KV kv_ok). exact (proj1 (Forall_forall _ _) HMF f0 Hf0).
Qed.

(* the stack window below sp the main entry states (MainEntry.amain_at: the start state's 6144513 bytes) *)
Hypothesis Hstk : AFm.stk SEGS m (usp - 6144513) usp.

(* the hidden argument ranges (MainEntry.hidden_arg): the envp array and the string area up to the
   stack VMA's end hold what the launch wrote *)
Hypothesis Hhid : forall a,
  (usp + 8 * argc + 16 <= a < usp + 8 * argc + 8 * envc + 24) \/
  (MEm.STR0_of (mkEntry sp brk0 mbase draw) inp <= a < bv_unsigned (SI.TOP draw)) ->
  m (Z_to_bv 64 a) = mem0 (Z_to_bv 64 a).

(* region 3 at the root: the launch's auxv at the run's own CONFIG_RSEQ value, or the region both values imply *)
Variable R3 : region.
Hypothesis HR3 : R3 = Auxv.Auxv.R3Tb_asan (la_rseq (SI.LA sp mbase inp)) \/ R3 = Auxv.Auxv.R3A_asan.

Lemma ev1 : bv_unsigned (ev E 1%uint63) = usp.
Proof. change (ev E 1%uint63) with (ev E0 1%uint63). unfold E0. rewrite InitLib.ev0_1. reflexivity. Qed.

Lemma noseg : forall a, SEGTOP <= a -> find_segment SEGS a 1 = None.
Proof. intros a Ha. apply (InitLib.find_segment_none SEGS a 1 SEGTOP segs_top); lia. Qed.

Lemma R0_bst : IMap.bst (rg_cells R0). Proof. unfold R0. cbn [rg_cells]. apply InitLib.imap_of_bst. Qed.
Lemma R1_bst : IMap.bst (rg_cells R1). Proof. unfold R1. cbn [rg_cells]. apply InitLib.imap_of_bst. Qed.
Lemma ev0A : ev E 0%uint63 = Z_to_bv 64 0.
Proof. change (ev E 0%uint63) with (ev E0 0%uint63). unfold E0. apply InitLib.ev0_0. Qed.

Lemma R0_ok : region_ok SEGS PRIV E m 0%uint63 R0.
Proof. exact (region0_ok SEGS V m E (B RZ) HB (NFS RZ w) HNF PRIV R0 R0_bst eq_refl ev0A Hminv (R0_cells_ok RZ w) COVER (COVER_tags_ok RZ w) COVER_sweep_ok). Qed.

Lemma R1_cov : range_covered_b R1 0 24 = true. Proof. vm_compute. reflexivity. Qed.

Lemma R1_valid : forall a, usp + -6144513 <= a < usp + 24 ->
  rb SEGS m a <> None /\ (rg_w R1 = true -> wb SEGS m a = true) /\ find_segment SEGS a 1 = None.
Proof.
  intros a Ha. pose proof usp_range as U. assert (NS : find_segment SEGS a 1 = None) by (apply noseg; unfold SEGTOP; lia).
  destruct (Z.lt_ge_cases a usp) as [Hl|Hg].
  - destruct Hstk as (_ & _ & Hs). destruct (Hs a ltac:(lia)) as [Hw (b & Hb)].
    split; [rewrite rb_mrd; unfold AM.wa; unfold AMm.wa in Hb; rewrite Hb; discriminate|]. split; [|exact NS].
    intros _. unfold wb. unfold AMm.wa in Hw. destruct (wview SEGS m (Z_to_bv 64 a)); [reflexivity| contradiction].
  - assert (R : rb SEGS m a <> None).
    { pose proof (range_covered_rb SEGS V m E (B RZ) HB (NFS RZ w) HNF 1%uint63 R1 (-6144513) 24 (R1_cells_ok RZ w) 0 24 R1_cov (a - usp) ltac:(lia)) as X.
      rewrite ev1 in X. replace (usp + (a - usp)) with a in X by lia. exact X. }
    split; [exact R|]. split; [|exact NS]. intros _. apply (wb_of_rb_noseg SEGS m a); [lia| exact R| exact NS].
Qed.

Lemma R1_ok : region_ok SEGS PRIV E m 1%uint63 R1.
Proof.
  pose proof usp_range as U.
  apply (based_region_ok SEGS V m E (B RZ) HB (NFS RZ w) HNF PRIV 1%uint63 R1 (-6144513) 24 eq_refl R1_bst eq_refl eq_refl).
  - rewrite ev1. lia.
  - rewrite ev1. rewrite two64_eq. lia.
  - rewrite ev1. exact R1_valid.
  - exact (R1_cells_ok RZ w).
  -
    intros o Ho _. unfold bg_byte. change (rg_bg R1) with BGNone. exact I.
Qed.

Lemma envc_range : 0 <= envc <= 256.
Proof. pose proof (SI.envc_range inp Hve) as H. unfold SI.envcZ, SI.nenvc in H. exact H. Qed.

Lemma hid_agree : forall a,
  (usp + 8 * argc + 16 <= a < usp + 8 * argc + 8 * envc + 24) \/
  (bv_unsigned (ev E0 5%uint63) <= a < bv_unsigned (SI.TOP draw)) ->
  rb SEGS m a = rb SEGS mem0 a /\ (wb SEGS mem0 a = true -> wb SEGS m a = true).
Proof. intros a Ha. rewrite <- STR0E in Ha. unfold rb, wb, wview. rewrite (Hhid a Ha). split; [reflexivity| intros W; exact W]. Qed.

Lemma R2_okA : region_ok SEGS PRIV E m 2%uint63 InitLib.R2T.
Proof.
  assert (R : region_ok SEGS [] E0 mem0 2%uint63 InitLib.R2T) by (unfold E0; unshelve (eapply (InitLib.R2_ok SEGS PCN PH SEGTOP segs_top segtop_low)); CLOSE).
  assert (H2 : hiZ E0 InitLib.R2T = 8 * SI.envcZ inp + 8) by (unfold E0; unshelve (eapply InitLib.hiZ_R2); CLOSE).
  apply (region_ok_transfer SEGS [] PRIV E0 E mem0 m 2%uint63 InitLib.R2T eq_refl R).
  - reflexivity.
  - reflexivity.
  - intros g gr c F. cbn in F. discriminate F.
  - intros o Ho. reflexivity.
  - intros a Ha. apply hid_agree. left.
    rewrite ev2E, H2, (InitLib.loZ_0 InitLib.R2T eq_refl) in Ha.
    unfold SI.envp_off, SI.argcZ, SI.envcZ, SI.nargc, SI.nenvc, SI.SP in Ha. fold usp argc envc in Ha. lia.
Qed.

Lemma R5_okA : region_ok SEGS PRIV E m 5%uint63 InitLib.R5T.
Proof.
  assert (R : region_ok SEGS [] E0 mem0 5%uint63 InitLib.R5T) by (unfold E0; unshelve (eapply (InitLib.R5_ok SEGS PCN PH SEGTOP segs_top segtop_low)); CLOSE).
  assert (H5 : hiZ E0 InitLib.R5T = Z.of_nat (length (hd [] argv)) + 1) by (unfold E0; unshelve (eapply InitLib.hiZ_R5); CLOSE).
  apply (region_ok_transfer SEGS [] PRIV E0 E mem0 m 5%uint63 InitLib.R5T eq_refl R).
  - reflexivity.
  - reflexivity.
  - intros g gr c F. cbn in F. discriminate F.
  - intros o Ho. reflexivity.
  - intros a Ha. apply hid_agree. right.
    rewrite H5, (InitLib.loZ_0 InitLib.R5T eq_refl) in Ha.
    pose proof ev5E as E5. pose proof topE as T. pose proof tot_a0 as TA. pose proof LSBZ as L. lia.
Qed.

Lemma R10_okA : region_ok SEGS PRIV E m 10%uint63 InitLib.R10T.
Proof.
  assert (R : region_ok SEGS [] E0 mem0 10%uint63 InitLib.R10T) by (unfold E0; unshelve (eapply (InitLib.R10_ok SEGS PCN PH SEGTOP segs_top segtop_low)); CLOSE).
  assert (H10 : hiZ E0 InitLib.R10T = Z.of_nat (length (hd [] (tl argv))) + 1) by (unfold E0; unshelve (eapply InitLib.hiZ_R10); CLOSE).
  apply (region_ok_transfer SEGS [] PRIV E0 E mem0 m 10%uint63 InitLib.R10T eq_refl R).
  - reflexivity.
  - reflexivity.
  - intros g gr c F. cbn in F. discriminate F.
  - intros o Ho. reflexivity.
  - intros a Ha. apply hid_agree. right.
    rewrite ev10E, H10, (InitLib.loZ_0 InitLib.R10T eq_refl) in Ha.
    pose proof ev5E as E5. pose proof topE as T. pose proof tot2 as T2. pose proof LSBZ as L. unfold SI.SP in E5, T, Ha. fold usp in E5, T, Ha. lia.
Qed.

Lemma R12_okA : region_ok SEGS PRIV E m 12%uint63 InitLib.R12T.
Proof.
  assert (R : region_ok SEGS [] E0 mem0 12%uint63 InitLib.R12T) by (unfold E0; unshelve (eapply (InitLib.R12_ok SEGS PCN PH SEGTOP segs_top segtop_low)); CLOSE).
  assert (H12 : hiZ E0 InitLib.R12T = Z.of_nat (length (SI.strarea inp))) by (unfold E0; unshelve (eapply InitLib.hiZ_R12); CLOSE).
  assert (SL : Z.of_nat (length (SI.strarea inp)) = Z.of_nat (SI.LSB inp) + 8) by (unshelve (eapply InitLib.strarea_len); CLOSE).
  apply (region_ok_transfer SEGS [] PRIV E0 E mem0 m 12%uint63 InitLib.R12T eq_refl R).
  - reflexivity.
  - reflexivity.
  - intros g gr c F. cbn in F. discriminate F.
  - intros o Ho. reflexivity.
  - intros a Ha. apply hid_agree. right.
    rewrite ev12E, H12, SL, (InitLib.loZ_0 InitLib.R12T eq_refl) in Ha.
    pose proof ev5E as E5. pose proof topE as T. unfold SI.SP in E5, T, Ha. fold usp in E5, T, Ha. lia.
Qed.

Lemma facts_E0 : facts_hold E0 FACTS0.
Proof.
  unfold E0, FACTS0, facts_hold. repeat apply Forall_cons; try apply Forall_nil.
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
  - unshelve (eapply InitLib.f_str_end); CLOSE.
  - unshelve (eapply InitLib.f_12_le_5); CLOSE.
  - unshelve (eapply InitLib.f_end5_12); CLOSE.
  - unshelve (eapply InitLib.f_sp_le_12); CLOSE.
  - unshelve (eapply InitLib.f_end12); CLOSE.
  - unshelve (eapply InitLib.f_12_le_10); CLOSE.
  - unshelve (eapply InitLib.f_end10_12); CLOSE.
  - unshelve (eapply InitLib.f_end2); CLOSE.
  - unshelve (eapply InitLib.f_end3); CLOSE.
  - unshelve (eapply InitLib.f_a0_end9); CLOSE.
  - unshelve (eapply InitLib.f_a0_base96); CLOSE.
  - unshelve (eapply InitLib.f_a1_end9); CLOSE.
  - unshelve (eapply InitLib.f_a1_base96); CLOSE.
Qed.

Definition stdvar (k : int) : bool :=
  match opq_get OPQ k with Some _ => false | None => match base_of DER k with Some _ => false | None => true end end.
Lemma evA_std : forall k, stdvar k = true -> ev E k = ev E0 k.
Proof.
  intros k H. cbn [ev E]. unfold evA. unfold stdvar in H. destruct (opq_get OPQ k); [discriminate|].
  destruct (base_of DER k); [discriminate| reflexivity].
Qed.
Lemma FACTS_std : forallb (fact_okb stdvar) FACTS0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma facts_E : facts_hold E FACTS0.
Proof. exact (facts_hold_agree stdvar E0 E evA_std eq_refl FACTS0 FACTS_std facts_E0). Qed.

(* region 3 at the run's own CONFIG_RSEQ value, from the main entry's facts ([R3_okb]): every cell but
   AT_EGID's by the facts on the vector's words, AT_EGID's as AT_GID's word ([InitLib.slot_bg_copy]), every
   byte readable by the vector's readable fact ([rd_chk]), the background read off the vector's bytes; the
   region both values imply holds wherever that one does ([InitLib.R3A_asan_of_R3Tb_asan]) *)
Lemma ev3A : bv_unsigned (ev E 3%uint63) = usp + 8 * argc + 8 * envc + 24.
Proof.
  change (ev E 3%uint63) with (ev E0 3%uint63). rewrite ev3E.
  unfold SI.auxv_off, SI.argcZ, SI.envcZ, SI.nargc, SI.nenvc, SI.SP. fold usp argc envc. lia.
Qed.
Lemma R3T_ok : region_ok SEGS PRIV E m 3%uint63 (Auxv.Auxv.R3Tb_asan (la_rseq (SI.LA sp mbase inp))).
Proof.
  pose proof usp_range as U. pose proof envc_range as EC. pose proof argc2 as A2. pose proof ev3A as E3.
  assert (HRZ : RZ = if la_rseq (SI.LA sp mbase inp) then 1 else 0)
    by (rewrite (SI.LA_rseq sp mbase inp); unfold RZ, MEm.RZ_of; destruct (kb_rseq (in_kernel inp)); reflexivity).
  pose proof (R3_ok_b (la_rseq (SI.LA sp mbase inp)) w) as X. rewrite <- HRZ in X.
  unfold R3_okb in X. apply andb_prop in X as [X XR]. apply andb_prop in X as [XC XE].
  pose proof (rd_chk_sound SEGS V m E (B RZ) HB (NFS RZ w) HNF _ _ _ XR) as RD.
  assert (HI : hiZ E (Auxv.Auxv.R3Tb_asan (la_rseq (SI.LA sp mbase inp))) = if la_rseq (SI.LA sp mbase inp) then 464 else 432)
    by (destruct (la_rseq (SI.LA sp mbase inp)); reflexivity).
  assert (HIr : 432 <= (if la_rseq (SI.LA sp mbase inp) then 464 else 432) <= 464)
    by (destruct (la_rseq (SI.LA sp mbase inp)); lia).
  assert (Bc : IMap.bst (rg_cells (Auxv.Auxv.R3Tb_asan (la_rseq (SI.LA sp mbase inp)))))
    by (unfold Auxv.Auxv.R3Tb_asan; cbn [rg_cells]; apply InitLib.imap_of_bst).
  apply (based_region_ok_slots SEGS PRIV E m 3%uint63 _ 0 _ eq_refl Bc eq_refl HI).
  - rewrite E3. lia.
  - rewrite E3, two64_eq. lia.
  - intros a Ha. split; [exact (RD a Ha)|]. split; [intros W; discriminate W|].
    apply noseg. unfold SEGTOP. lia.
  - intros g gr F.
    pose proof (proj1 (forallb_forall _ _) XC (g, gr) (proj2 (IMap.elements_spec g gr _ Bc) F)) as Y. cbv beta in Y. cbn [fst] in Y.
    revert Y. destruct (PrimInt63.eqb g 45%uint63) eqn:G; intros Y.
    + apply Uint63.eqb_correct in G. subst g.
      assert (GR : gr = Gran false [Cell 0%uint63 8%uint63 (VBg false 3%uint63 (wp Auxv.Auxv.GID_OFF) 8%uint63)]).
      { revert F. destruct (la_rseq (SI.LA sp mbase inp)); intros F; vm_compute in F; injection F as <-; reflexivity. }
      subst gr. cbn [g_cells]. split.
      * destruct (copy_chk_sound SEGS V m E (B RZ) HB (NFS RZ w) HNF 3%uint63 360 344 XE) as (W & H2 & H1).
        apply (InitLib.slot_bg_copy SEGS E m (bv_unsigned (ev E 3%uint63)) _ 3%uint63 (wp Auxv.Auxv.GID_OFF) W).
        -- intros o. reflexivity.
        -- change (w2Zs (wp Auxv.Auxv.GID_OFF)) with 344. exact H2.
        -- change (8 * keyZ 45%uint63) with 360. exact H1.
      * destruct (la_rseq (SI.LA sp mbase inp)); vm_compute; reflexivity.
    + cbn [orb] in Y. unfold granb_chk in Y. apply andb_prop in Y as [Y1 Y2]. cbn [fst snd] in Y1, Y2.
      split; [exact (gran_chk_sound SEGS V m E (B RZ) HB (NFS RZ w) HNF _ _ _ Y1) | exact Y2].
  - intros o Ho Hunc. eapply bg_unk_ok; [reflexivity | intros o'; reflexivity |].
    apply RD. lia.
Qed.
Lemma hiZ_R3Tb : forall b, hiZ E (Auxv.Auxv.R3Tb_asan b) = Z.of_nat (auxv_size b).
Proof. intros [|]; reflexivity. Qed.
Lemma R3_shape : rg_w R3 = false /\ loZ R3 = 0 /\ 432 <= hiZ E R3 <= Z.of_nat (auxv_size (la_rseq (SI.LA sp mbase inp))).
Proof.
  pose proof auxszE as AX. pose proof RZ_range as RR.
  destruct HR3 as [E3 | E3]; rewrite E3; (split; [reflexivity|]); (split; [reflexivity|]).
  - rewrite hiZ_R3Tb. lia.
  - change (hiZ E Auxv.Auxv.R3A_asan) with 432. lia.
Qed.
Lemma R3_okA : region_ok SEGS PRIV E m 3%uint63 R3.
Proof. destruct HR3 as [E3 | E3]; rewrite E3; [exact R3T_ok | exact (InitLib.R3A_asan_of_R3Tb_asan _ _ _ _ _ R3T_ok)]. Qed.

(* the auxv's end bound at region 3's own size, and the main entry's facts at region 3 *)
Lemma end3_E : fact_holds E (Regen.Regen.end3_fact R3).
Proof.
  assert (F : fact_holds E0 (Regen.Regen.end3_fact R3)).
  { destruct HR3 as [E3 | E3]; rewrite E3; [rewrite InitLib.end3_R3Tb_asan | rewrite InitLib.end3_R3A_asan];
    unfold E0; [unshelve (eapply InitLib.f_end3T) | unshelve (eapply InitLib.f_end3A)]; CLOSE. }
  exact (fact_holds_agree stdvar E0 E evA_std eq_refl (Regen.Regen.end3_fact R3) eq_refl F).
Qed.
Lemma facts_R3 : facts_hold E (FACTS R3).
Proof.
  unfold FACTS, facts_hold. apply Forall_forall. intros f' Hf'. apply in_map_iff in Hf' as (f & <- & Hf).
  pose proof (proj1 (Forall_forall _ _) facts_E f Hf) as H.
  unfold Regen.Regen.fix_end3. match goal with |- fact_holds E (if ?c then _ else _) => destruct c end; [exact end3_E | exact H].
Qed.

Lemma ev20 : bv_unsigned (ev E 20%uint63) = 4096 * V 0%nat + 512 * V 10%nat + 2 * V 6%nat + 2147450880.
Proof.
  pose proof HB as H. unfold B in H. apply Forall_app in H as [_ H]. apply Forall_app in H as [H _]. unfold DER in H.
  inversion H as [|x l H1 _]; subst. cbn [fst snd] in H1. rewrite H1. unfold leval. cbn [fst snd lsum]. lia.
Qed.
Lemma ev64 : bv_unsigned (ev E 64%uint63) = V 44%nat.
Proof.
  pose proof HB as H. unfold B in H. apply Forall_app in H as [_ H]. apply Forall_app in H as [_ H].
  apply Forall_app in H as [H _]. unfold OPQ in H. cbn [map] in H.
  inversion H as [|x l H1 _]; subst. cbn [fst snd] in H1. rewrite H1. unfold leval, lvar. cbn [fst snd lsum]. lia.
Qed.

Lemma RSH_ok : region_ok SEGS PRIV E m 20%uint63 RSH.
Proof.
  pose proof usp_range as U. pose proof (HV 0%nat) as R0. pose proof (HV 6%nat) as R6. pose proof (HV 10%nat) as R10.
  apply (zero_region_ok SEGS V m E (B RZ) HB (NFS RZ w) HNF PRIV 20%uint63 RSH (-768064) 3 F_STK eq_refl (F_STK_in RZ w) eq_refl
           (InitLib.imap_of_bst _ _) eq_refl eq_refl eq_refl eq_refl); rewrite ?ev20.
  - lia.
  - rewrite two64_eq. lia.
  - unfold F_STK, leval. cbn [nf_a fst snd lsum]. lia.
  - unfold zlen, F_STK, leval. cbn [nf_kind nf_a nf_v fst snd lsum]. lia.
  - intros a Ha. apply noseg. unfold SEGTOP. lia.
Qed.

Lemma shmap_main : forall a, IMGSH_LO <= a < IMGSH_LO + IMGSH_LEN -> wb SEGS m a = true.
Proof.
  intros a Ha. pose proof (proj1 (Forall_forall _ _) HMF _ (IMGSH_in RZ w)) as W. cbn [MXm.mfact_ok MXm.zv] in W.
  destruct W as (_ & _ & W). specialize (W (a - IMGSH_LO) ltac:(lia)). replace (IMGSH_LO + (a - IMGSH_LO)) with a in W by lia.
  unfold wb. unfold AMm.wa in W. destruct (wview SEGS m (Z_to_bv 64 a)); [reflexivity | congruence].
Qed.

Lemma zro_main : forall a, IMGSH_LO <= a < IMGSH_LO + ZRO_LEN -> m (Z_to_bv 64 a) = Some (Z_to_bv 8 0) /\ wb SEGS m a = true.
Proof.
  intros a Ha. split; [| apply shmap_main; unfold ZRO_LEN, IMGSH_LEN in *; lia].
  pose proof (proj1 (Forall_forall _ _) HMF _ (ZRO_in RZ w)) as Zf. cbn [MXm.mfact_ok MXm.zv] in Zf.
  specialize (Zf (a - IMGSH_LO) ltac:(lia)). replace (IMGSH_LO + (a - IMGSH_LO)) with a in Zf by lia. exact Zf.
Qed.
Lemma zsh_main : forall a, ZSH_LO <= a < ZSH_HI -> m (Z_to_bv 64 a) = Some (Z_to_bv 8 0) /\ wb SEGS m a = true.
Proof.
  intros a Ha. split; [| apply shmap_main; unfold ZSH_LO, ZSH_HI, IMGSH_LO, IMGSH_LEN in *; lia].
  pose proof (proj1 (Forall_forall _ _) HMF _ (ZSHF_in RZ w)) as Zf. cbn [MXm.mfact_ok MXm.zv] in Zf.
  specialize (Zf (a - ZSHF_LO) ltac:(unfold ZSH_LO, ZSH_HI, ZSHF_LO, ZSHF_LEN in *; lia)). replace (ZSHF_LO + (a - ZSHF_LO)) with a in Zf by lia. exact Zf.
Qed.

Lemma zpb_main : forall a, ZPB_LO <= a < ZPB_HI -> m (Z_to_bv 64 a) = Some (Z_to_bv 8 0) /\ wb SEGS m a = true.
Proof.
  intros a Ha. split; [| apply shmap_main; unfold ZPB_LO, ZPB_HI, IMGSH_LO, IMGSH_LEN in *; lia].
  pose proof (proj1 (Forall_forall _ _) HMF _ (ZPBF_in RZ w)) as Zf. cbn [MXm.mfact_ok MXm.zv] in Zf.
  specialize (Zf (a - ZPBF_LO) ltac:(unfold ZPB_LO, ZPB_HI, ZPBF_LO, ZPBF_LEN in *; lia)). replace (ZPBF_LO + (a - ZPBF_LO)) with a in Zf by lia. exact Zf.
Qed.

Lemma pool_main : forall i, 0 <= i < 8 -> rb SEGS m (POOL_FL + i) = Some (Z_to_bv 8 0).
Proof.
  intros i Hi. pose proof (POOL_fresh_ok RZ w) as C. apply existsb_exists in C as (f & Hf & FC).
  pose proof (fact_cell_sound SEGS V m (lconst POOL_FL) 8 (lconst 0) f (proj1 (Forall_forall _ _) HNF f Hf) FC i Hi) as RB.
  rewrite !leval_lconst in RB. rewrite byte_of_zero in RB by lia. exact RB.
Qed.

Lemma gsh_main : forall a n v, In (a, n, v) GSH_TAB -> forall i, 0 <= i < n -> m (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 v).
Proof.
  intros a n v Hin i Hi. pose proof (proj1 (forallb_forall _ _) (GSH_tab_ok RZ w) _ Hin) as C. unfold gsh_ent_chk in C.
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
  intros a Ha. pose proof (proj1 (Forall_forall _ _) HMF _ (F_MWRS_in RZ w)) as W. unfold F_MWRS in W. cbn [MXm.mfact_ok MXm.zv] in W.
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
  pose proof (proj1 (Forall_forall _ _) HMF _ (F_MZS_in RZ w)) as Zf. unfold F_MZS in Zf. cbn [MXm.mfact_ok MXm.zv] in Zf.
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

Local Ltac REG := eapply (word_is_sv V E (B RZ) HB); [vm_compute; reflexivity | unfold leval; cbn [fst snd lsum]; f_equal; pose proof Pusp; pose proof argc2; lia].

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

Lemma REGS_bst : IMap.bst (REGS R3). Proof. unfold REGS. apply InitLib.imap_of_bst. Qed.

Lemma regs_cases : forall k r, IMap.find k (REGS R3) = Some r ->
  (k = 0%uint63 /\ r = R0) \/ (k = 1%uint63 /\ r = R1) \/ (k = 2%uint63 /\ r = InitLib.R2T) \/ (k = 3%uint63 /\ r = R3)
  \/ (k = 5%uint63 /\ r = InitLib.R5T) \/ (k = 10%uint63 /\ r = InitLib.R10T) \/ (k = 12%uint63 /\ r = InitLib.R12T)
  \/ (k = 20%uint63 /\ r = RSH).
Proof.
  intros k r H. apply (InitLib.find_in_elements _ k r (REGS R3) REGS_bst) in H. rewrite REGS_elements in H.
  assert (EL : REGS_L R3 = [(0%uint63, R0); (1%uint63, R1); (2%uint63, InitLib.R2T); (3%uint63, R3); (5%uint63, InitLib.R5T);
                            (10%uint63, InitLib.R10T); (12%uint63, InitLib.R12T); (20%uint63, RSH)]) by (vm_compute; reflexivity).
  rewrite EL in H. cbn [In] in H. intuition congruence.
Qed.

Lemma based_apart : forall k r, IMap.find k (REGS R3) = Some r -> k <> 0%uint63 -> k <> 1%uint63 ->
  rg_w r = false /\ (usp + 32 <= bv_unsigned (ev E k) + loZ r \/ bv_unsigned (ev E k) + hiZ E r <= usp - 8388608).
Proof.
  intros k r H K0 K1. pose proof envc_range as EC. pose proof argc2 as A2. pose proof usp_range as U.
  pose proof HEADZ as HZ. pose proof RZ_range as RR. pose proof (HV 11%nat) as V11. pose proof (HV 4%nat) as V4.
  pose proof R3_shape as (W3 & L3 & H3).
  destruct (regs_cases k r H) as [[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]]]]]; try congruence;
    (split; [first [reflexivity | exact W3]|]).
  - left. change (ev E 2%uint63) with (ev E0 2%uint63). rewrite ev2E.
    rewrite (InitLib.loZ_0 InitLib.R2T eq_refl). unfold SI.envp_off, SI.argcZ, SI.nargc, SI.SP. fold usp argc. lia.
  - left. change (ev E 3%uint63) with (ev E0 3%uint63). rewrite ev3E, L3.
    unfold SI.auxv_off, SI.argcZ, SI.envcZ, SI.nargc, SI.nenvc, SI.SP. fold usp argc envc. lia.
  - left. change (ev E 5%uint63) with (ev E0 5%uint63). rewrite ev5E.
    rewrite (InitLib.loZ_0 InitLib.R5T eq_refl). unfold SI.SP. fold usp. lia.
  - left. change (ev E 10%uint63) with (ev E0 10%uint63). rewrite ev10E.
    rewrite (InitLib.loZ_0 InitLib.R10T eq_refl). unfold SI.SP. fold usp. lia.
  - left. change (ev E 12%uint63) with (ev E0 12%uint63). rewrite ev12E.
    rewrite (InitLib.loZ_0 InitLib.R12T eq_refl). unfold SI.SP. fold usp. lia.
  - right. rewrite ev20. change (hiZ E RSH) with 3. pose proof (HV 0%nat). pose proof (HV 6%nat). pose proof (HV 10%nat). pose proof Pusp. lia.
Qed.

Lemma based_hull : forall a, in_based E (REGS R3) a -> BHULL sp draw a.
Proof.
  intros a B0. destruct B0 as (k & r & Hk & K & Ha).
  pose proof envc_range as EC. pose proof argc2 as A2. pose proof usp_range as U. pose proof topE as T. pose proof LSBZ as L.
  pose proof ev5E as E5. rewrite Nat2Z.inj_add in E5. unfold SI.SP in T, E5. fold usp in T, E5.
  pose proof tot2 as T2.
  destruct (regs_cases k r Hk) as [[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]]]]]; try discriminate K.
  -   left. rewrite ev1 in Ha. change (loZ R1) with (-6144513) in Ha. change (hiZ E R1) with 24 in Ha.
      pose proof HEADZ. pose proof RZ_range. pose proof (HV 11%nat). pose proof (HV 4%nat). lia.
  -   left. change (ev E 2%uint63) with (ev E0 2%uint63) in Ha. rewrite ev2E in Ha. rewrite (InitLib.loZ_0 InitLib.R2T eq_refl) in Ha.
    change (hiZ E InitLib.R2T) with (hiZ E0 InitLib.R2T) in Ha.
    assert (H2 : hiZ E0 InitLib.R2T = 8 * SI.envcZ inp + 8) by (unfold E0; unshelve (eapply InitLib.hiZ_R2); CLOSE).
    rewrite H2 in Ha. pose proof HEADZ. pose proof RZ_range. pose proof (HV 11%nat). pose proof (HV 4%nat).
    unfold SI.envp_off, SI.argcZ, SI.envcZ, SI.nargc, SI.nenvc, SI.SP in Ha. fold usp argc envc in Ha. lia.
  -   left. pose proof R3_shape as (_ & L3 & H3). change (ev E 3%uint63) with (ev E0 3%uint63) in Ha. rewrite ev3E, L3 in Ha.
    pose proof HEADZ. pose proof auxszE. pose proof RZ_range. pose proof (HV 11%nat). pose proof (HV 4%nat).
    unfold SI.auxv_off, SI.argcZ, SI.envcZ, SI.nargc, SI.nenvc, SI.SP in Ha. fold usp argc envc in Ha. lia.
  -   left. change (ev E 5%uint63) with (ev E0 5%uint63) in Ha. rewrite (InitLib.loZ_0 InitLib.R5T eq_refl) in Ha.
    change (hiZ E InitLib.R5T) with (hiZ E0 InitLib.R5T) in Ha.
    assert (H5 : hiZ E0 InitLib.R5T = Z.of_nat (length (hd [] argv)) + 1) by (unfold E0; unshelve (eapply InitLib.hiZ_R5); CLOSE).
    rewrite H5 in Ha. lia.
  -   left. change (ev E 10%uint63) with (ev E0 10%uint63) in Ha. rewrite ev10E in Ha. rewrite (InitLib.loZ_0 InitLib.R10T eq_refl) in Ha.
    change (hiZ E InitLib.R10T) with (hiZ E0 InitLib.R10T) in Ha.
    assert (H10 : hiZ E0 InitLib.R10T = Z.of_nat (length (hd [] (tl argv))) + 1) by (unfold E0; unshelve (eapply InitLib.hiZ_R10); CLOSE).
    rewrite H10 in Ha. unfold SI.SP in Ha. fold usp in Ha. lia.
  -   left. change (ev E 12%uint63) with (ev E0 12%uint63) in Ha. rewrite ev12E in Ha. rewrite (InitLib.loZ_0 InitLib.R12T eq_refl) in Ha.
    change (hiZ E InitLib.R12T) with (hiZ E0 InitLib.R12T) in Ha.
    assert (H12 : hiZ E0 InitLib.R12T = Z.of_nat (length (SI.strarea inp))) by (unfold E0; unshelve (eapply InitLib.hiZ_R12); CLOSE).
    assert (SL : Z.of_nat (length (SI.strarea inp)) = Z.of_nat (SI.LSB inp) + 8) by (unshelve (eapply InitLib.strarea_len); CLOSE).
    rewrite H12, SL in Ha. unfold SI.SP in Ha. fold usp in Ha. rewrite Nat2Z.inj_add in Ha. lia.
  -   right. rewrite ev20 in Ha. change (loZ RSH) with (-768064) in Ha. change (hiZ E RSH) with 3 in Ha.
    pose proof (HV 0%nat). pose proof (HV 6%nat). pose proof (HV 10%nat).
    assert (D : usp / 8 = 4096 * V 0%nat + 512 * V 10%nat + 2 * V 6%nat) by (symmetry; apply (Z.div_unique _ 8 _ 0); lia).
    fold usp. rewrite D. lia.
Qed.

Lemma fx_acc_hull : forall a, fx_acc SEGS E (REGS R3) a -> HULL sp draw a.
Proof. intros a [B0|S]; [right; exact (based_hull a B0)| left; exact S]. Qed.

Definition ROOT_with (R3 : region) (os : list opinst) : sstate := SS MAINPC RFA FFA RNone (REGS R3) (FACTS R3 ++ FACTS_TW) os PRIV 128%uint63.
Theorem main_st_ok_ops : forall (OPS : optable) (mo : Model) (os : list opinst),
  op_minv OPS mo -> ops_hold OPS E os m mo -> ops_apart SEGS OPS E os (REGS R3) PRIV ->
  (forall a, fx_acc SEGS E (REGS R3) a -> op_cov OPS (insts E os) a) ->
  st_ok SEGS OPS E (ROOT_with R3 os) ms mo.
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
      [exact R0_ok | exact R1_ok | exact R2_okA | exact R3_okA | exact R5_okA | exact R10_okA | exact R12_okA | exact RSH_ok].
  - intros k1 r1 k2 r2 H1 H2 Hne Hk1 Hk2 Hw a [Ha1 Ha2].
    assert (S1 : forall r, IMap.find 1%uint63 (REGS R3) = Some r -> r = R1).
    { intros r Hr. destruct (regs_cases _ r Hr) as [[X _]|[[_ ->]|[[X _]|[[X _]|[[X _]|[[X _]|[[X _]|[X _]]]]]]]]; try discriminate X. reflexivity. }
    assert (K0 : forall k, PrimInt63.eqb k 0%uint63 = false -> k <> 0%uint63) by (intros k Hk ->; discriminate Hk).
    destruct (PrimInt63.eqb k1 1%uint63) eqn:E1; [apply Uint63.eqb_correct in E1; subst k1| apply Uint63.eqb_false_spec in E1; rename E1 into N1];
    (destruct (PrimInt63.eqb k2 1%uint63) eqn:E2; [apply Uint63.eqb_correct in E2; subst k2| apply Uint63.eqb_false_spec in E2; rename E2 into N2]).
    + apply Hne. reflexivity.
    + rewrite (S1 r1 H1) in Ha1. destruct (based_apart k2 r2 H2 (K0 _ Hk2) N2) as [_ L]. rewrite ev1 in Ha1. change (hiZ E R1) with 24 in Ha1.
      change (loZ R1) with (-6144513) in Ha1. lia.
    + rewrite (S1 r2 H2) in Ha2. destruct (based_apart k1 r1 H1 (K0 _ Hk1) N1) as [_ L]. rewrite ev1 in Ha2. change (hiZ E R1) with 24 in Ha2.
      change (loZ R1) with (-6144513) in Ha2. lia.
    + destruct (based_apart k1 r1 H1 (K0 _ Hk1) N1) as [W1 _]. destruct (based_apart k2 r2 H2 (K0 _ Hk2) N2) as [W2 _].
      destruct Hw as [Hw|Hw]; congruence.
  - intros r g gr c Hr Hg Hc i Hi.
    assert (r = R0). { destruct (regs_cases _ r Hr) as [[_ ->]|[[X _]|[[X _]|[[X _]|[[X _]|[[X _]|[[X _]|[X _]]]]]]]]; try discriminate X. reflexivity. }
    subst r. exact (cells_public0 SEGS (B RZ) (NFS RZ w) PRIV R0 R0_bst (R0_cells_ok RZ w) g gr c Hg Hc i Hi).
  - unfold facts_hold. apply Forall_app. split; [exact facts_R3| exact facts_TW].
  - rewrite Hms. cbn [ASTm.MS ms_mem]. exact Hops.
  - exact Hapart.
  - exact Hmi.
  - exact Hcov.
  - rewrite Hms. cbn [ASTm.MS ms_mem]. intros a b Hab seg Hseg. pose proof (Hminv a b Hab) as R. unfold AMm.ro_addr in R. rewrite Hseg in R.
    destruct (seg_writable seg); [reflexivity| discriminate R].
Qed.

Theorem main_st_ok : forall (OPS : optable) (mo : Model),
  op_minv OPS mo ->
  (forall a, fx_acc SEGS E (REGS R3) a -> op_cov OPS [] a) ->
  st_ok SEGS OPS E (ROOT R3) ms mo.
Proof. intros OPS mo Hmi Hcov. exact (main_st_ok_ops OPS mo [] Hmi (Forall_nil _) (Forall_nil _) Hcov). Qed.

End Main.

(* the main entry's state (MainEntry.amain_at) as the section's hypotheses *)
Lemma amain_hyps : forall (en : ExecEntry) (inp : ProcInput) (ms : machine_state) (mo : Model),
  valid_argv (in_argv inp) -> valid_sp (en_sp en) -> entry_launch_ok_va Sv48 en inp ->
  MEm.amain_at en inp ms mo ->
  exists (w : bool) (V : nat -> Z) (m : word -> option byte),
    ms = ASTm.MS (AFm.mkR (Z_to_bv 64 MEm.ARA) (Z_to_bv 64 (bv_unsigned (en_sp en) - 48)) (Z_to_bv 64 MEm.AGP) (Z_to_bv 64 MEm.ATP)
                 (Z_to_bv 64 (V 856%nat)) (Z_to_bv 64 (V 857%nat)) (Z_to_bv 64 (V 858%nat))
                 (Z_to_bv 64 (bv_unsigned (en_sp en) + 8)) (Z_to_bv 64 (Z.of_nat (length (in_argv inp)))) (Z_to_bv 64 (Z.of_nat (length (in_argv inp)))) (Z_to_bv 64 (bv_unsigned (en_sp en) + 8))
                 (Z_to_bv 64 (bv_unsigned (en_sp en) + 8 * Z.of_nat (length (in_argv inp)) + 16)) (Z_to_bv 64 0x6000000000000000)
                 (Z_to_bv 64 (V 859%nat)) (Z_to_bv 64 (V 860%nat)) (Z_to_bv 64 (V 861%nat)) (Z_to_bv 64 (V 862%nat))
                 (Z_to_bv 64 MEm.AMAIN) (Z_to_bv 64 (bv_unsigned (en_sp en) + 8 * Z.of_nat (length (in_argv inp)) + 16))
                 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                 (Z_to_bv 64 (V 863%nat)) (Z_to_bv 64 (V 864%nat)) (Z_to_bv 64 (V 865%nat)) (Z_to_bv 64 (V 866%nat)))
            bvmap_empty (Z_to_bv 64 MEm.AMAIN) (Z_to_bv 32 0) None m (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.seg_rom SEGS)
    /\ (forall n, 0 <= V n < 2 ^ 64)
    /\ 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat = bv_unsigned (en_sp en)
    /\ V 1%nat = Z.of_nat (length (in_argv inp)) /\ V 2%nat = Z.of_nat (length (in_envp inp))
    /\ V 3%nat = Z.of_nat (length (nth 0 (in_argv inp) []))
    /\ V 4%nat = Z.of_nat (SI.pad (en_sp en) (en_mmap_base en) inp (en_draw en))
    /\ 8 * V 11%nat = Z.of_nat (SI.gap inp)
    /\ V 8%nat = bv_unsigned (in_uid inp) /\ V 9%nat = bv_unsigned (in_hwcap inp)
    /\ 1 <= V 44%nat <= 4194303
    /\ Forall (MXm.mfact_ok SEGS V m) (MEm.amf (MEm.RZ_of inp) w)
    /\ AMm.mem_inv SEGS m
    /\ AFm.stk SEGS m (bv_unsigned (en_sp en) - 6144513) (bv_unsigned (en_sp en))
    /\ (forall a,
         (bv_unsigned (en_sp en) + 8 * Z.of_nat (length (in_argv inp)) + 16 <= a
            < bv_unsigned (en_sp en) + 8 * Z.of_nat (length (in_argv inp)) + 8 * Z.of_nat (length (in_envp inp)) + 24) \/
         (MEm.STR0_of en inp <= a < bv_unsigned (SI.TOP (en_draw en))) ->
         m (Z_to_bv 64 a) = SI.mem0 SEGS PCN PH (en_sp en) (en_mmap_base en) inp (en_draw en) (Z_to_bv 64 a)).
Proof.
  intros [sp brk0 mbase draw] inp ms mo Hva Hsp Hlau HM. cbn [en_sp en_brk en_mmap_base en_draw] in *.
  destruct HM as (w & V & m & Hms & HV & (P0 & P6 & P10 & Pusp & P1 & P2 & P3 & P7 & P4 & P5 & P8 & P9 & P11) & HMF & HPF & Hminv & Hstk & Hhid & _ & _).
  exists w, V, m. split; [exact Hms|]. split; [exact HV|]. split; [exact Pusp|].
  split; [exact P1|]. split; [exact P2|]. split; [exact P3|].
  split. { rewrite P4. unfold MEm.Wpad, SI.pad, SI.TOP. cbn [en_sp en_draw]. rewrite (SI.LA_rseq sp mbase inp). reflexivity. }
  split. { rewrite P11. unfold SI.gap. lia. }
  split; [exact P8|]. split; [exact P9|].
  split.
  { apply (proj1 (Forall_forall _ _) HPF (MXm.PVar 44 1 4194303)).
    unfold MEm.apf; destruct w; destruct (Z.eqb (MEm.RZ_of inp) 1); vm_compute; repeat first [left; reflexivity | right]. }
  split; [exact HMF|]. split; [exact Hminv|]. split; [exact Hstk|].
  intros a Ha. etransitivity; [apply (Hhid a)| reflexivity].
  unfold MEm.hidden_arg. cbv zeta. exact Ha.
Qed.

Theorem amain_st_ok_ops : forall (xb0 : int -> list byte) (en : ExecEntry) (inp : ProcInput) (ms : machine_state) (mo : Model) (R3 : region),
  valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_sp (en_sp en) ->
  entry_launch_ok_va Sv48 en inp -> valid_hwcap (in_hwcap inp) -> valid_launch inp ->
  length (in_argv inp) = 2%nat ->
  MEm.amain_at en inp ms mo ->
  R3 = Auxv.Auxv.R3Tb_asan (la_rseq (SI.LA (en_sp en) (en_mmap_base en) inp)) \/ R3 = Auxv.Auxv.R3A_asan ->
  exists E : env,
    eb E = eb (InitLib.E0 PCN PH (en_sp en) (en_mmap_base en) inp (en_draw en) xb0) /\
    (forall a, fx_acc SEGS E (REGS R3) a -> HULL (en_sp en) (en_draw en) a) /\
    (forall a, in_based E (REGS R3) a -> (bv_unsigned (en_sp en) - 6144513 <= a < 2 ^ 47)
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
    forall (OPS : optable) (os : list opinst), op_minv OPS mo -> ops_hold OPS E os (ms_mem ms) mo -> ops_apart SEGS OPS E os (REGS R3) PRIV ->
      (forall a, fx_acc SEGS E (REGS R3) a -> op_cov OPS (insts E os) a) -> st_ok SEGS OPS E (ROOT_with R3 os) ms mo.
Proof.
  intros xb0 [sp brk0 mbase draw] inp ms mo R3 Hva Hve Hsp Hlau Hhw Hvl Hargc2 HM HR3. cbn [en_sp en_brk en_mmap_base en_draw] in *.
  destruct (amain_hyps (mkEntry sp brk0 mbase draw) inp ms mo Hva Hsp Hlau HM)
    as (w & V & m & Hms & HV & Pusp & P1 & P2 & P3 & P4 & P11 & P8 & P9 & Ptid & HMF & Hminv & Hstk & Hhid).
  cbn [en_sp en_brk en_mmap_base en_draw] in *.
  exists (E xb0 sp mbase inp draw V m). split; [reflexivity|]. split.
  { intros a Ha. eapply fx_acc_hull; eassumption. }
  split.
  { intros a Ha.
    assert (T47 : bv_unsigned (SI.TOP draw) <= 2 ^ 47) by (pose proof (top_hi sp brk0 mbase inp draw Hlau); lia).
    assert (BH : BHULL sp draw a) by (eapply based_hull; eassumption).
    destruct BH as [BH|BH]; [left; lia| right; exact BH]. }
  split; [apply ev1|].
  assert (EM : ms_mem ms = m) by (rewrite Hms; reflexivity).
  rewrite EM.
  split; [eapply shmap_main; eassumption|].
  split; [eapply zro_main; eassumption|].
  split; [eapply zsh_main; eassumption|].
  split; [eapply zpb_main; eassumption|].
  split; [intros a0 n0 v0 Hin0 i0 Hi0; eapply gsh_main; eassumption|].
  split; [eapply pool_main; eassumption|].
  split; [eapply ssh_main; eassumption|].
  split; [eapply zarg_main; eassumption|].
  intros OPS os Hmi Hops Hapart Hcov.
  eapply main_st_ok_ops; eassumption.
Qed.

Theorem amain_st_ok : forall (xb0 : int -> list byte) (en : ExecEntry) (inp : ProcInput) (ms : machine_state) (mo : Model) (R3 : region),
  valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_sp (en_sp en) ->
  entry_launch_ok_va Sv48 en inp -> valid_hwcap (in_hwcap inp) -> valid_launch inp ->
  length (in_argv inp) = 2%nat ->
  MEm.amain_at en inp ms mo ->
  R3 = Auxv.Auxv.R3Tb_asan (la_rseq (SI.LA (en_sp en) (en_mmap_base en) inp)) \/ R3 = Auxv.Auxv.R3A_asan ->
  exists E : env,
    eb E = eb (InitLib.E0 PCN PH (en_sp en) (en_mmap_base en) inp (en_draw en) xb0) /\
    (forall a, fx_acc SEGS E (REGS R3) a -> HULL (en_sp en) (en_draw en) a) /\
    forall OPS : optable, op_minv OPS mo -> (forall a, fx_acc SEGS E (REGS R3) a -> op_cov OPS [] a) -> st_ok SEGS OPS E (ROOT R3) ms mo.
Proof.
  intros xb0 en inp ms mo R3 Hva Hve Hsp Hlau Hhw Hvl Hargc2 HM HR3.
  destruct (amain_st_ok_ops xb0 en inp ms mo R3 Hva Hve Hsp Hlau Hhw Hvl Hargc2 HM HR3) as (E & EB & HU & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FIN).
  exists E. split; [exact EB|]. split; [exact HU|].
  intros OPS Hmi Hcov. exact (FIN OPS [] Hmi (Forall_nil _) (Forall_nil _) Hcov).
Qed.

End InitAsan2.
