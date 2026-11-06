(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec Tac Arr Bytes ZBridge ITree Nodes Decode SysStep MonadX Image ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pcap_err__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_next_ex.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_open.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_fopen.TwB.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Ubsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


(* [comment removed for export] *)
Lemma lxor_lit_range : forall W M, (0 <= W < 2^64)%Z -> (0 <= M < 2^64)%Z -> (0 <= Z.lxor W M < 2^64)%Z.
Proof.
  intros W M HW HM. split; [apply Z.lxor_nonneg; lia|].
  destruct (Z.eq_dec (Z.lxor W M) 0) as [E|Hnz]; [rewrite E; lia|].
  assert (Hp : (0 < Z.lxor W M)%Z) by (pose proof (Z.lxor_nonneg W M); lia).
  apply (proj2 (Z.log2_lt_pow2 (Z.lxor W M) 64 Hp)).
  eapply Z.le_lt_trans; [apply Z.log2_lxor; lia|].
  apply Z.max_lub_lt.
  - destruct (Z.eq_dec W 0) as [->|E]; [cbn; lia| apply Z.log2_lt_pow2; lia].
  - destruct (Z.eq_dec M 0) as [->|E]; [cbn; lia| apply Z.log2_lt_pow2; lia].
Qed.
(* [comment removed for export] *)
Lemma seqz_xor_lit : forall W M, (0 <= W < 2^64)%Z -> (0 <= M < 2^64)%Z ->
  v_sltiu (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 W)) M)) 1 = Z_to_bv 64 (if W =? M then 1 else 0)%Z.
Proof.
  intros W M HW HM. unfold v_sltiu. rewrite (unsigned_lit W) by lia.
  pose proof (lxor_lit_range W M HW HM) as R. rewrite (unsigned_lit (Z.lxor W M)) by exact R.
  change (bv_wrap 64 1) with 1%Z.
  destruct (Z.eqb_spec W M) as [->|NE].
  - rewrite Z.lxor_nilpotent. reflexivity.
  - destruct (Z.ltb_spec (Z.lxor W M) 1) as [LT|GE]; [|reflexivity].
    exfalso. apply NE. apply Z.lxor_eq. pose proof (Z.lxor_nonneg W M). lia.
Qed.
(* [comment removed for export] *)
Lemma snez_xor_lit : forall W M, (0 <= W < 2^64)%Z -> (0 <= M < 2^64)%Z ->
  v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 W)) M)) = Z_to_bv 64 (if W =? M then 0 else 1)%Z.
Proof.
  intros W M HW HM. rewrite v_sltu_b2z. rewrite (unsigned_lit W) by lia. rewrite (unsigned_lit 0) by lia.
  pose proof (lxor_lit_range W M HW HM) as R. rewrite (unsigned_lit (Z.lxor W M)) by exact R.
  destruct (Z.eqb_spec W M) as [->|NE].
  - rewrite Z.lxor_nilpotent. reflexivity.
  - destruct (Z.ltb_spec 0 (Z.lxor W M)) as [LT|GE]; [reflexivity|].
    exfalso. apply NE. apply Z.lxor_eq. pose proof (Z.lxor_nonneg W M). lia.
Qed.
(* [comment removed for export] *)
Lemma seqz_lit : forall x, (0 <= x < 2^64)%Z -> v_sltiu (Z_to_bv 64 x) 1 = Z_to_bv 64 (if x =? 0 then 1 else 0)%Z.
Proof.
  intros x Hx. unfold v_sltiu. rewrite unsigned_lit by lia. change (bv_wrap 64 1) with 1%Z.
  destruct (Z.eqb_spec x 0) as [->|NE]; [reflexivity|]. destruct (Z.ltb_spec x 1); [exfalso; lia| reflexivity].
Qed.
(* [comment removed for export] *)
Lemma slli1_flag : forall c, (0 <= c < 2^62)%Z -> Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 c)) 1) = Z_to_bv 64 (2 * c)%Z.
Proof. intros c Hc. rewrite unsigned_lit by lia. rewrite Z.shiftl_mul_pow2 by lia. f_equal. lia. Qed.

(* [comment removed for export] *)
Ltac lit_branch := let K := fresh "Klit" in if_cases K; try (vm_compute in K; discriminate K); clear K.

Section WithCeil.
Context {CEILV : CEIL}.
Section Chk.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.

  (* [comment removed for export] *)
  Definition chk_ctx (sp tp : word) (R : rctx) (s : PState H hptr) (CL FB : list cblock) (lo MG FA EB ERR : Z) (f : hptr) (magic : list Z) (m : mem) : Prop :=
    GIo K R s CL FB m /\ (usp0 R - 8388608 <= lo)%Z /\ (lo + 81920 <= bv_unsigned sp)%Z /\ (bv_unsigned sp <= rc_spmain R)%Z
    /\ tp = rc_tp R /\ (bv_unsigned sp mod 16 = 0)%Z
    /\ In (f, FA, FILE_BLOCK) FB /\ sites = sites_at (bv_unsigned sp + D_CHECK_HEADER)
    /\ length magic = 4%nat /\ Forall (fun z => 0 <= z < 256)%Z magic
    /\ (bv_unsigned sp <= ERR)%Z /\ (ERR + 4 <= MG)%Z /\ (MG + 4 <= rc_spmain R)%Z
    /\ (bv_unsigned sp <= EB)%Z /\ (EB + 256 <= rc_spmain R)%Z /\ (EB + 256 <= ERR \/ MG + 4 <= EB)%Z /\ (ERR mod 4 = 0)%Z /\ (EB mod 8 = 0)%Z.

  (* [comment removed for export] *)
  Lemma chk_fail0 :
    forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (R : rctx) (s : PState H hptr) (CL FB : list cblock) (lo MG FA EB ERR : Z) (f : hptr) (magic : list Z) (m : mem)
           (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' t3' t4' t5' t6' : word) (m3 : mem) (ps3 : PState H hptr)
           (msg : list Z) (junk3 : list byte) (ew : word) (hc : list cell),
      chk_ctx sp tp R s CL FB lo MG FA EB ERR f magic m ->
      mem_inv usegs m3 -> stk usegs m3 lo (bv_unsigned sp + -96) ->
      agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m3 ->
      GIo K R ps3 CL FB m3 ->
      rw_cells usegs m3 (bv_unsigned sp + -96) hc -> cells_size hc = 24%nat ->
      rw_cells usegs m3 (bv_unsigned sp + -72) [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells usegs m3 ERR [C4 ew] -> rw_cells usegs m3 MG (map (fun z => C1 (Z_to_bv 8 z)) magic) ->
      rw_cells usegs m3 EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk3] -> (Z.of_nat (length msg) < 256)%Z ->
      Forall (fun z => 0 < z < 256)%Z msg -> ps_outfile ps3 = ps_outfile s ->
      evt usegs (check_header_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL FB lo MG EB ERR magic f m (ps_outfile s) (CH_Err msg) ps3)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0' t1' t2' (Z_to_bv 64 ERR) (Z_to_bv 64 EB) (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                 s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x157b8) fc None m3 (seg_rom usegs)).
  Proof using HFL SFL. pin_using (fun (HFL SFL : unit) => tt).
    intros until hc. intros CTX MIx ST3 AG3 G3 FA3 Hhc FRS3 ERR3 MG3 HEB3 LEN3 RNG3 OFX.
    destruct CTX as (G & LO & BU & SPM & TP & ALN & HinF & SITES & GL & GR & R1 & R2 & R3 & E1 & E2 & D1 & E4 & E8).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. pose proof (bv_unsigned_in_range 64 sp) as RSP.
    destruct (rw_cells_forget _ _ _ _ FA3) as [fj FA3']. clear FA3. rewrite Hhc in FA3'.
    hide HEB3. hide MG3.
    pose proof (munch_refl [(ERR, ERR + 4)]%Z m3) as MU3. pose proof (wmono_refl usegs m3) as WM3.
    do 13 pstep.
    release_frame FA3' ST3 (bv_unsigned sp + -72)%Z. release_frame FRS3 ST3 (bv_unsigned sp).
    unhide HEB3. unhide MG3.
    destruct magic as [|k0 [|k1 [|k2 [|k3 [|? ?]]]]]; try discriminate GL. cbn [map] in MG3.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (AGW : agrees_on (fun a => outside [(ERR, ERR + 4)]%Z a) m3 mm) by (eapply agrees_on_of_munch; [exact MU3 | exact WM3 | intros a _ Ho; exact Ho]);
      assert (HEB' : rw_cells usegs mm EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk3])
        by (eapply agrees_rw_cells; [exact AGW | exact HEB3 | intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia]);
      assert (MG' : rw_cells usegs mm MG [CB 4 (map b8 [k0; k1; k2; k3])])
        by (eapply rw_cells_recell; [eapply agrees_rw_cells; [exact AGW | exact MG3 | intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia] | cbn; repeat split; exact Logic.I | reflexivity]);
      assert (G' : GIo K R ps3 CL FB mm)
        by (eapply (GIo_client_frame K HFL SFL); [exact G3 | exact MU3 | exact WM3 |]; apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil])
    end.
    apply evt_done. unfold check_header_post.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists (Z_to_bv 64 0), mm, (Z_to_bv 64 1) end.
    split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
    split; [solve [assumption | congruence] |].
    split; [assumption|]. split; [assumption|].
    split. { eapply agrees_on_trans; [exact AG3|]. eapply agrees_on_weaken; [exact AGW|]. intros a [_ [_ Hn]]; cbn [outside]; lia. }
    split; [exact MG'|]. split; [assumption|].
    exists junk3. split; [reflexivity|]. split; [reflexivity|]. split; [exact G'|]. split; [exact HEB'|]. split; [exact LEN3| exact RNG3].
  Qed.

  (* [comment removed for export] *)
  Lemma chk_fail :
    forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (R : rctx) (s : PState H hptr) (CL FB : list cblock) (lo MG FA EB ERR : Z) (f : hptr) (magic : list Z) (m : mem)
           (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' t3' t4' t5' t6' : word) (m3 : mem) (ps3 : PState H hptr)
           (msg : list Z) (junk3 : list byte) (ew : word) (hc : list cell),
      chk_ctx sp tp R s CL FB lo MG FA EB ERR f magic m ->
      mem_inv usegs m3 -> stk usegs m3 lo (bv_unsigned sp + -96) ->
      agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m3 ->
      GIo K R ps3 CL FB m3 ->
      rw_cells usegs m3 (bv_unsigned sp + -96) hc -> cells_size hc = 24%nat ->
      rw_cells usegs m3 (bv_unsigned sp + -72) [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells usegs m3 ERR [C4 ew] -> rw_cells usegs m3 MG (map (fun z => C1 (Z_to_bv 8 z)) magic) ->
      rw_cells usegs m3 EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk3] -> (Z.of_nat (length msg) < 256)%Z ->
      Forall (fun z => 0 < z < 256)%Z msg -> ps_outfile ps3 = ps_outfile s ->
      evt usegs (check_header_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL FB lo MG EB ERR magic f m (ps_outfile s) (CH_Err msg) ps3)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0' t1' t2' (Z_to_bv 64 ERR) (Z_to_bv 64 EB) a0' a1' a2' a3' a4' a5' a6' a7'
                 s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x157b4) fc None m3 (seg_rom usegs)).
  Proof using HFL SFL. pin_using (fun (HFL SFL : unit) => tt).
    intros until hc. intros CTX MIx ST3 AG3 G3 FA3 Hhc FRS3 ERR3 MG3 HEB3 LEN3 RNG3 OFX.
    hide HEB3. hide MG3. hide FA3. hide FRS3. hide ERR3.
    pose proof (munch_refl ([] : list (Z * Z)) m3) as MU3. pose proof (wmono_refl usegs m3) as WM3.
    step.
    unhide HEB3. unhide MG3. unhide FA3. unhide FRS3. unhide ERR3.
    eapply chk_fail0; eassumption.
  Qed.

  (* [comment removed for export] *)
  Definition z8 : list byte := repeat (Z_to_bv 8 0) 8.
  Definition fd_pad48 : list byte := repeat (Z_to_bv 8 0) 24 ++ le4 (Z_to_bv 64 (-1)) ++ repeat (Z_to_bv 8 0) 20.
  Definition blank_cells (P : Z) : list cell :=
    [ C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
      CB 12 (repeat (Z_to_bv 8 0) 12); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF)); C4 (Z_to_bv 64 0);
      CB 4 (repeat (Z_to_bv 8 0) 4); CB 8 z8; CB 16 (repeat (Z_to_bv 8 0) 16);
      C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
      CB 12 (repeat (Z_to_bv 8 0) 12); C8 (Z_to_bv 64 0); CB 28 (repeat (Z_to_bv 8 0) 28); C4 (Z_to_bv 64 0);
      CB 48 fd_pad48;
      C8 (Z_to_bv 64 0); CB 304 (repeat (Z_to_bv 8 0) 304);
      C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
      CB 72 (repeat (Z_to_bv 8 0) 72); CB 8 z8; C8 (Z_to_bv 64 0); CB 8 z8; C8 (Z_to_bv 64 0);
      C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0) ].

  Lemma blank_recell : forall m P,
    rw_cells usegs m P ([CB 16 (repeat (Z_to_bv 8 0) 16); C4 (Z_to_bv 64 (-1)); CB 28 (repeat (Z_to_bv 8 0) 28);
                         C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF)); CB 128 (repeat (Z_to_bv 8 0) 128); C4 (Z_to_bv 64 (-1));
                         CB (Z.to_nat (PCAP_SF_TOTAL - 188)) (repeat (Z_to_bv 8 0) (Z.to_nat (PCAP_SF_TOTAL - 188)))]) ->
    rw_cells usegs m P (blank_cells P).
  Proof using Type. pin_using tt.
    intros m P Hc.
    destruct (rw_cells_cut _ _ _ 3 Hc) as [A X]. destruct (rw_cells_cut _ _ _ 1 X) as [B C]. clear Hc X.
    cbn [firstn skipn cells_size csize Nat.add] in A, B, C.
    unfold PCAP_SF_TOTAL in C. change (Z.to_nat (664 - 188)) with 476%nat in C.
    assert (A' : rw_cells usegs m P (firstn 7 (blank_cells P))).
    { eapply rw_cells_recell; [exact A | cbn; repeat split; exact Logic.I | vm_compute; reflexivity]. }
    assert (C' : rw_cells usegs m (P + Z.of_nat 48 + Z.of_nat 8) (skipn 8 (blank_cells P))).
    { eapply rw_cells_recell; [exact C | cbn; repeat split; exact Logic.I | unfold fd_pad48; vm_compute; reflexivity]. }
    pose proof (rw_cells_uncut _ _ _ _ _ A' B ltac:(cbn; lia)) as AB.
    pose proof (rw_cells_uncut _ _ _ _ _ AB C' ltac:(cbn; lia)) as ABC. exact ABC.
  Qed.

  (* [comment removed for export] *)
  Definition pcells (P : Z) (sw : bool) (maj min lt ext : Z) (nxt bsz buf snapc clean hsz lsw scl : cell) : list cell :=
    [ C8 (Z_to_bv 64 0); nxt; C4 (Z_to_bv 64 (-1)); bsz; buf; CB 12 (repeat (Z_to_bv 8 0) 12); C4 (Z_to_bv 64 0);
      C8 (Z_to_bv 64 (P + 648)); C4 (Z_to_bv 64 (Z.b2z sw)); CB 4 (repeat (Z_to_bv 8 0) 4); CB 8 z8; CB 16 (repeat (Z_to_bv 8 0) 16);
      C4 (Z_to_bv 64 maj); C4 (Z_to_bv 64 min); snapc; C4 (Z_to_bv 64 lt); C4 (Z_to_bv 64 ext);
      CB 12 (repeat (Z_to_bv 8 0) 12); C8 (Z_to_bv 64 0); CB 28 (repeat (Z_to_bv 8 0) 28); C4 (Z_to_bv 64 0);
      CB 48 fd_pad48; C8 (Z_to_bv 64 0); CB 304 (repeat (Z_to_bv 8 0) 304);
      C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
      CB 72 (repeat (Z_to_bv 8 0) 72); CB 8 z8; C8 (Z_to_bv 64 0); CB 8 z8; clean; hsz; lsw; scl ].
  Definition blank_junk : pcap_junk :=
    mkPJ (Z_to_bv 64 0) (Z_to_bv 64 (-1)) (repeat (Z_to_bv 8 0) 12) (repeat (Z_to_bv 8 0) 4) (repeat (Z_to_bv 8 0) 16)
         (repeat (Z_to_bv 8 0) 12) (repeat (Z_to_bv 8 0) 28) fd_pad48 (repeat (Z_to_bv 8 0) 304) (repeat (Z_to_bv 8 0) 72) (Z_to_bv 64 0).

  Hypothesis HPL : heap_perm_law K.
  Hypothesis MALLOC : malloc_stmt_o HO K.
  Hypothesis FREE : free_stmt_o HO K.

  (* [comment removed for export] *)
  Lemma blocks2_apart : forall R s bq B BS q P PS CL FB m,
    GIo K R s ((bq, B, BS) :: (q, P, PS) :: CL) FB m -> (1 <= BS)%Z -> (1 <= PS)%Z -> (B + BS <= P \/ P + PS <= B)%Z.
  Proof using Type. pin_using tt.
    intros R s bq B BS q P PS CL FB m G HBS HPS.
    destruct (Z.le_gt_cases (B + BS) P) as [|Hlt]; [left; lia|]. destruct (Z.le_gt_cases (P + PS) B) as [|Hlt']; [right; lia|]. exfalso.
    destruct (Z.le_gt_cases P B) as [Hpb|Hpb].
    - destruct (GIo_CLc_facts K R s [(bq, B, BS)] ((q, P, PS) :: CL) FB m B G
                 ltac:(unfold in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia)) as [_ Hn].
      apply Hn. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia.
    - destruct (GIo_CLc_facts K R s [(bq, B, BS)] ((q, P, PS) :: CL) FB m P G
                 ltac:(unfold in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia)) as [_ Hn].
      apply Hn. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia.
  Qed.

End Chk.

End WithCeil.
