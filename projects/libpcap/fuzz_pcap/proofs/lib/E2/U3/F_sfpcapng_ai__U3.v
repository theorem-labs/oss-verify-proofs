(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool String Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Arr Bytes ITree Nodes Decode SysStep MonadX Image ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memmove__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pcap_err__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcap_chkA__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_aiE__S3.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require KeepHyps.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ZBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3 Require F_sfpcap_chkF__U3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_sfpcapng_ai.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep MonadX Image ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memmove__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pcap_err__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcap_chkA__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_aiE__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memmove__S3.F_memmove.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface_ng.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_small.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_open.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_fopen.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_aiD.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_aiC.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.TwB.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Ubsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import KeepHyps.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import KeepHyps.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac gio_ceil_fact :=
  match goal with
  | G : GIo _ _ _ _ _ _ |- _ => let H := fresh "CLO__" in pose proof (S3.PcapRep.TwB.GIo_ceil_lo _ _ _ _ _ _ G) as H; unfold rc_lo in H
  end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try gio_ceil_fact; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Lemma snez_pos : forall x, (0 < x < 2^64)%Z -> v_sltu z64 (Z_to_bv 64 x) = Z_to_bv 64 1.
Proof using Type. pin_using tt.
  intros x Hx. rewrite v_sltu_b2z. change (bv_unsigned z64) with 0%Z. rewrite (unsigned_lit x) by lia.
  destruct (Z.ltb_spec 0 x); [reflexivity| exfalso; lia].
Qed.
Lemma seqz_pos : forall x, (0 < x < 2^64)%Z -> v_sltiu (Z_to_bv 64 x) 1 = Z_to_bv 64 0.
Proof using Type. pin_using tt.
  intros x Hx. unfold v_sltiu. rewrite (unsigned_lit x) by lia. change (bv_wrap 64 1) with 1%Z.
  destruct (Z.ltb_spec x 1); [exfalso; lia| reflexivity].
Qed.

Lemma get_le32_at pre v0 v1 v2 v3 rest :
  get_le32 (pre ++ v0 :: v1 :: v2 :: v3 :: rest) (Z.of_nat (length pre)) = le4val v0 v1 v2 v3.
Proof using Type. pin_using tt.
  unfold get_le32. change (pre ++ v0 :: v1 :: v2 :: v3 :: rest) with (pre ++ [v0; v1; v2; v3] ++ rest).
  change 4%Z with (Z.of_nat (length [v0; v1; v2; v3])). rewrite zslice_at. cbn -[Z.add Z.mul]. unfold le4val. lia.
Qed.

Lemma le4_s32_lit x0 x1 x2 x3 : 0 <= x0 < 256 -> 0 <= x1 < 256 -> 0 <= x2 < 256 -> 0 <= x3 < 256 ->
  le4 (Z_to_bv 64 (s32 (le4val x0 x1 x2 x3))) = [Z_to_bv 8 x0; Z_to_bv 8 x1; Z_to_bv 8 x2; Z_to_bv 8 x3].
Proof using Type. pin_using tt.
  intros. unfold s32, le4val.
  destruct (Z.lt_ge_cases (x0 + 256 * x1 + 65536 * x2 + 16777216 * x3) (2^31)) as [LT|GE].
  - apply (le4_of_val _ x0 x1 x2 x3 0); try lia. rewrite unsigned_lit by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia.
  - apply (le4_of_val _ x0 x1 x2 x3 (2^32 - 1)); try lia. rewrite unsigned_lit_wrap. Z.div_mod_to_equations; lia.
Qed.

Section AI.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation PS := (PState H hptr).
  #[local] Notation pcapT := (PcapTypes.pcap hptr hptr).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis MALLOCS : malloc_stmt_o HO K.
  Hypothesis REALLOC : realloc_stmt_o HO K.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.

  Open Scope bv_scope.

  Definition add_interface_proof__stmt : Prop := add_interface_stmt HO K sites.
  Section Sz3.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R st C1 C2 FB P B I CUR EB lo idb_off p s i c bs ej pad cpad : ltac2:(SecDiet.SzSec.tyM 'add_interface_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma add_interface_proof__body : ltac2:(SecDiet.SzSec.bodyP 'add_interface_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using HFL HPL MALLOCS REALLOC SFL SNPRINTF. pin_using (fun (HFL HPL MALLOCS REALLOC SFL SNPRINTF : unit) => tt).
 intros PRE HS HinP HinB APB -> -> -> -> HPV HNG HIF UTS WMB HBUF PFX LENB GRD HCUR CUR1 CUR2 CUR8 IDB0 IDB4 COFF CREM CEND CBT HEB EBR.
    destruct PRE as (G & ST & LO & BU & SPM & MI & TP & ALN).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPWC. pose proof (proj1 SPWC) as SPW. pose proof (GIo_sp47 K _ _ _ _ _ G) as SP47. unfold rc_lo in LO. unfold ADD_INTERFACE_STACK, MALLOC_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2^64)%Z in RSP.
    (* [comment removed for export] *)
    assert (HinP' : In (pc_self p, P, PCAP_NG_SF_TOTAL) ((C1 ++ IBLK i I s ++ C2) ++ FB)).
    { apply in_or_app. left. apply in_app_iff in HinP as [X|X]; apply in_or_app; [left; exact X| right; apply in_or_app; right; exact X]. }
    assert (HinB' : In (pc_buffer p, B, pc_bufalloc p) ((C1 ++ IBLK i I s ++ C2) ++ FB)).
    { apply in_or_app. left. apply in_app_iff in HinB as [X|X]; apply in_or_app; [left; exact X| right; apply in_or_app; right; exact X]. }
    assert (HinP'' : In (pc_self p, P, PCAP_NG_SF_TOTAL) (C1 ++ IBLK i I s ++ C2)).
    { apply in_app_iff in HinP as [X|X]; apply in_or_app; [left; exact X| right; apply in_or_app; right; exact X]. }
    pose proof (GIo_block_ok K _ _ _ _ _ _ G HinP') as (P1 & P2 & P3 & P4 & P5 & _). cbn [cb_addr cb_size fst snd] in P1, P2, P3, P4, P5. unfold PCAP_NG_SF_TOTAL in P4, P5.
    pose proof (GIo_block_ok K _ _ _ _ _ _ G HinB') as (B1 & B2 & B3 & B4 & _). cbn [cb_addr cb_size fst snd] in B1, B2, B3, B4.
    assert (P14 : (0 < P /\ P + 680 <= CEILZ)%Z) by (split; [exact P1| exact P4]).
    assert (B14 : (0 < B /\ B + pc_bufalloc p <= CEILZ)%Z) by (split; [exact B1| exact B4]).
    unfold PCAP_NG_SF_TOTAL in APB.
    assert (P5' : out_of_image P 680) by (unfold out_of_image; exact P5).
    assert (CLB : forall a, in_block (C1 ++ C2) a -> (a < CEILZ)%Z).
    { intros a Ha. apply in_block_app in Ha. destruct (GIo_CLc_facts K R st (C1 ++ IBLK i I s ++ C2) [] FB m a ltac:(rewrite app_nil_r; exact G)) as [Hc _]; [| lia].
      apply in_block_app. destruct Ha as [Ha|Ha]; [left; exact Ha| right; apply in_block_app; right; exact Ha]. }
    assert (INPc : forall a, (P <= a < P + 680)%Z -> in_block (C1 ++ C2) a).
    { intros a Ha. apply in_block_In. exists (pc_self p, P, PCAP_NG_SF_TOTAL). split; [exact HinP|]. cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia. }
    assert (INBc : forall a, (B <= a < B + pc_bufalloc p)%Z -> in_block (C1 ++ C2) a).
    { intros a Ha. apply in_block_In. exists (pc_buffer p, B, pc_bufalloc p). split; [exact HinB|]. cbn [cb_addr cb_size fst snd]. lia. }
    (* [comment removed for export] *)
    assert (EBX : ((bv_unsigned sp <= EB /\ EB + 256 <= rc_spmain R /\ (EB + 256 <= CUR \/ CUR + 24 <= EB)) \/ (EB = P + 216))%Z) by (destruct EBR as [X|X]; [left| right]; lia).
    clear EBR.
    assert (EB64 : (0 < EB /\ EB + 256 < 2^64)%Z) by (unfold rc_spmain in EBX; destruct EBX as [X| ->]; lia).
    assert (CRE : client_range R (C1 ++ C2) (bv_unsigned sp) EB 256).
    { destruct EBX as [X| ->]; [right; lia| left]. intros a Ha. apply INPc. lia. }
    assert (EBiv : client_iv R (C1 ++ C2) (EB, (EB + 256)%Z)).
    { destruct EBX as [X| ->]; [left; cbn [fst snd]; unfold rc_lo; lia| right]. unfold iv_in_block. apply Exists_exists. exists (pc_self p, P, PCAP_NG_SF_TOTAL). split; [exact HinP|]. cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia. }
    pose proof (rw_cells_bound _ _ _ _ HEB) as BEB. cbn [cells_size csize Nat.add] in BEB.
    (* [comment removed for export] *)
    unfold ifaces_ok in HIF. rewrite HS in HIF.
    assert (IFC : (0 <= ng_ifcount s /\ ng_ifcount s <= ng_ifaces_size s /\ ng_ifaces_size s < 2^26 /\ ng_ifcount s = Z.of_nat (length (ng_ifaces s)))%Z).
    { destruct i as [q|]; [destruct HIF as (js & tail & LJS & AR & E1 & E2 & E3 & IFW0); lia| destruct HIF as (-> & E0 & E1 & E2); rewrite E0, E1, E2; cbn; lia]. }
    (* [comment removed for export] *)
    unfold add_interface. unfold ng_of, ng_ifaces_ptr_of. rewrite HS.
    cbn [mo_bind mo_ret mo_unr MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_malloc e_realloc prims pc_bufdata pc_swapped set_ng set_priv].
    replace (u32 (ng_ifcount s + 1)) with (ng_ifcount s + 1)%Z by (unfold u32; symmetry; apply Z.mod_small; lia).
    replace (u32 (ng_ifaces_size s * 2) <? ng_ifaces_size s) with false by (unfold u32; rewrite Z.mod_small by lia; symmetry; apply Z.ltb_ge; lia).
    unfold ADD_INTERFACE_ENTRY.
    pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    assert (P8 : (P mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r P); apply aligned16_8; [exact P2| reflexivity]).
    pose proof (aligned16_8 P 648 P2 eq_refl) as P648.
    assert (BI4 : ((B + idb_off) mod 4 = 0)%Z) by (clear - B2 IDB4; Z.div_mod_to_equations; lia).
    assert (BIR : (0 < B + idb_off /\ B + idb_off + 8 <= CEILZ)%Z) by (clear - B1 B4 IDB0 COFF CREM CEND LENB; lia).
    hide HEB. hide HBUF. hide HCUR. hide HNG. hide HPV.
    ienter. carve_frame 112%nat ST. do 15 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (G0 : GIo K R st (C1 ++ IBLK i I s ++ C2) FB mm)
        by (eapply (GIo_client_frame K HFL SFL); [exact G | exact MU | exact WM |]; apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]);
      assert (AG0 : agrees_on (fun a => outside [(bv_unsigned sp - 112, bv_unsigned sp)]%Z a) m mm)
        by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
      rename mm into m0
    end.
    clear MU WM.
    assert (T0 : forall A cs, rw_cells usegs m A cs -> (A + Z.of_nat (cells_size cs) <= bv_unsigned sp - 112 \/ bv_unsigned sp <= A)%Z -> rw_cells usegs m0 A cs).
    { intros A cs HC HA. eapply agrees_rw_cells; [exact AG0 | exact HC | intros a Ha; cbn [outside]; lia]. }
    unhide HEB. unhide HBUF. unhide HCUR. unhide HNG. unhide HPV. pose proof HPV as HPVm.
    apply T0 in HEB; [|cbn [cells_size csize Nat.add]; destruct EBX as [X| ->]; lia].
    apply T0 in HBUF; [|cbn [cells_size csize Nat.add]; lia].
    apply T0 in HCUR; [|unfold cursor_cells; cbn [cells_size csize Nat.add]; lia].
    apply T0 in HNG; [|unfold ng_cells, PCAP_PRIV_OFF; cbn [cells_size csize Nat.add]; lia].
    apply T0 in HPV; [|cbn [cells_size csize Nat.add]; lia].
    assert (AGa : ai_AGP sp C1 C2 P B CUR EB p m m0).
    { eapply agrees_on_weaken; [exact AG0|]. intros a [[Ha|Ha] _]; cbn [outside]; [lia| pose proof (CLB a Ha); lia]. }
    (* [comment removed for export] *)
    destruct (rw_cells_cut _ _ _ 1 FR) as [HD FRS]. clear FR. cbn [firstn skipn cells_size csize Nat.add] in HD, FRS.
    replace (bv_unsigned sp + -112 + Z.of_nat 8)%Z with (bv_unsigned sp + -104)%Z in FRS by lia.
    (* [comment removed for export] *)
    unfold PCAP_PRIV_OFF in HPV, HNG. unfold ng_cells in HNG. unfold cursor_cells in HCUR.
    hide HEB. hide HBUF. hide HCUR. hide HD. hide FRS.
    (* [comment removed for export] *)
    step. rewrite (and7_aligned P) by (clear - P1 P4 P8; lia). step. if_false.
    step.
    step. if_false_by (eqz_false (P + 648) ltac:(clear - P1 P4; lia)). step. rewrite (and7_aligned (P + 648)) by (clear - P1 P4 P648; lia). step. if_false.
    step. rewrite (sx32_small (ng_ifcount s)) by lia. step. rewrite (sx32_small (ng_ifaces_size s)) by lia.
    step. rewrite (unsigned_lit (ng_ifcount s)), (bv_swrap32_small (ng_ifcount s + 1)) by lia.
    pose proof (munch_refl [(P + 660, P + 664)]%Z m0) as MU1. pose proof (wmono_refl usegs m0) as WM1.
    hide HPV. step. unhide HPV.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    assert (AGS1 : agrees_on (fun a => outside [(P + 660, P + 664)]%Z a) m0 m1) by (eapply agrees_on_of_munch; [exact MU1 | exact WM1 | intros a _ Ho; exact Ho]).
    assert (G1 : GIo K R st (C1 ++ IBLK i I s ++ C2) FB m1).
    { eapply (GIo_client_frame K HFL SFL); [exact G0 | exact MU1 | exact WM1 |]. apply Forall_cons; [| apply Forall_nil]. right. unfold iv_in_block. apply Exists_exists.
      exists (pc_self p, P, PCAP_NG_SF_TOTAL). split; [exact HinP'' |]. cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia. }
    clear MU1 WM1.
    (* [comment removed for export] *)
    assert (KED0 : forall (ra' t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' y2 y3 y4 y5 : word) (m2 : mem) (stG : PS) (sg : pcap_ng_sf) (q1 : hptr) (I' : Z)
                          (js : list if_junk) (pad1 junk1 : list byte) (hd : list cell),
      ng_user_tsresol sg = ng_user_tsresol s -> ng_max_blocksize sg = ng_max_blocksize s -> ng_ifaces sg = ng_ifaces s ->
      (ng_ifcount sg = Z.of_nat (length (ng_ifaces s)) + 1)%Z -> (ng_ifcount sg <= ng_ifaces_size sg)%Z -> (1 <= ng_ifaces_size sg < 2^26)%Z ->
      length js = length (ng_ifaces s) -> Forall if_wf (ng_ifaces s) ->
      mem_inv usegs m2 -> stk usegs m2 lo (bv_unsigned sp + -112) -> ai_AGP sp C1 C2 P B CUR EB p m m2 ->
      rw_cells usegs m2 (bv_unsigned sp + -112) hd -> cells_size hd = 8%nat ->
      rw_cells usegs m2 (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells usegs m2 (P + 48) [C8 (Z_to_bv 64 (P + 648)); C4 (Z_to_bv 64 (Z.b2z (pc_swapped p)))] ->
      rw_cells usegs m2 B [CB (Z.to_nat (pc_bufalloc p)) bs] ->
      rw_cells usegs m2 CUR [C8 (Z_to_bv 64 (B + cur_off c)); C8 (Z_to_bv 64 (cur_remaining c)); C4 (Z_to_bv 64 (cur_block_type c)); CB 4 cpad] ->
      rw_cells usegs m2 EB [CB 256 ej] ->
      rw_cells usegs m2 (P + 648) (ng_cells sg I' pad1) ->
      rw_cells usegs m2 I' (ifs_cells (rev (ng_ifaces s)) js) ->
      rw_cells usegs m2 (I' + 40 * (ng_ifcount sg - 1)) [CB (Z.to_nat (40 * (ng_ifaces_size sg - (ng_ifcount sg - 1)))) junk1] ->
      GIo K R stG ((q1, I', 40 * ng_ifaces_size sg)%Z :: C1 ++ C2) FB m2 -> ps_outfile stG = ps_outfile st ->
      evt usegs (POSTQ (ai_result idb_off p s c sg (Some q1) (process_idb_options (pc_swapped p) c (pc_bufdata p))) stG)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0' t1' t2' (Z_to_bv 64 EB) (Z_to_bv 64 (P + 648))
                 (Z_to_bv 64 P) (Z_to_bv 64 (B + idb_off)) (Z_to_bv 64 CUR) a3' a4' a5' a6' a7'
                 y2 y3 y4 y5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (Z_to_bv 64 0x175f8) fc None m2 (seg_rom usegs))).
    { intros until hd. intros U1 U2 U5 IC1 IC2 SZ LJS IFW MI2 ST2 AG2 HD2 Hhd FR2 HPV2 BUF2 CC2 HEB2 NG2 AR1 JK G2 OFG.
      clear HNG HPV G0 AGa G1 AGS1 HIF.
      pose proof (GIo_block_ok K _ _ _ _ _ _ G2 ltac:(left; reflexivity)) as (Q1 & Q2 & Q3 & Q4 & _). cbn [cb_addr cb_size fst snd] in Q1, Q2, Q3, Q4.
      pose proof (head_apart K _ _ _ _ _ _ _ G2 HinB) as APIB. pose proof (head_apart K _ _ _ _ _ _ _ G2 HinP) as APIP. cbn [cb_addr cb_size fst snd] in APIB, APIP. unfold PCAP_NG_SF_TOTAL in APIP.
      pose proof (rw_cells_bound _ _ _ _ AR1) as BA1. rewrite ifs_cells_size in BA1 by (rewrite length_rev; lia). rewrite length_rev in BA1.
      remember (I' + 40 * (ng_ifcount sg - 1))%Z as SA eqn:HSA.
      (* [comment removed for export] *)
      destruct (split_at4 (pc_bufdata p) (Z.to_nat (idb_off + 4)) ltac:(lia)) as (pre0 & x0 & x1 & x2 & x3 & post0 & Ebuf & Lpre0).
      assert (GX : (0 <= x0 < 256 /\ 0 <= x1 < 256 /\ 0 <= x2 < 256 /\ 0 <= x3 < 256)%Z).
      { rewrite Ebuf in GRD. apply Forall_app in GRD as [_ GB].
        pose proof (Forall_inv GB) as X0. pose proof (Forall_inv (Forall_inv_tail GB)) as X1. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail GB))) as X2.
        pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail GB)))) as X3. cbv beta in X0, X1, X2, X3. lia. }
      destruct GX as (X0 & X1 & X2 & X3).
      assert (SNAP : ai_snap idb_off p = le4val x0 x1 x2 x3).
      { unfold ai_snap. rewrite Ebuf. replace (idb_off + 4)%Z with (Z.of_nat (length pre0)) by lia. apply get_le32_at. }
      assert (SNR : (0 <= ai_snap idb_off p < 2^32)%Z) by (rewrite SNAP; unfold le4val; lia).
      pose proof PFX as PFX0. rewrite Ebuf in PFX0.
      destruct (pfx_decomp pre0 [x0; x1; x2; x3] post0 bs PFX0) as (bsr0 & Ebs & _). cbn [map] in Ebs.
      pose proof BUF2 as BX. rewrite Ebs in BX.
      pose proof (rw_cells_recell _ _ _ [CB (length pre0) (map b8 pre0); C4 (Z_to_bv 64 (le4val x0 x1 x2 x3)); CB (length bsr0) bsr0] BX
                    ltac:(cbn; rewrite length_map; repeat split; reflexivity) ltac:(cbn [cells_bytes cbytes app]; rewrite le4_lit by lia; rewrite !app_nil_r; cbn [app]; reflexivity)) as BX'.
      destruct (rw_cells_cut _ _ _ 1 BX') as [_ BX2]. destruct (rw_cells_cut _ _ _ 1 BX2) as [HSN _]. clear BX BX' BX2. cbn [firstn skipn cells_size csize Nat.add app] in HSN.
      lazymatch type of HSN with rw_cells _ _ ?A _ => replace A with (B + idb_off + 4)%Z in HSN by lia end.
      (* [comment removed for export] *)
      pose proof (rw_cells_split_CB _ _ _ [] _ _ [] [4%nat; 36%nat; Z.to_nat (40 * (ng_ifaces_size sg - ng_ifcount sg))] JK ltac:(cbn; lia)) as JK'. clear JK.
      cbn [mk_CB_cells app] in JK'.
      assert (SAR : (I' <= SA /\ SA + 40 <= CEILZ /\ SA mod 8 = 0)%Z).
      { rewrite HSA. split; [clear - IC1 IC2 SZ Q1; lia|]. split; [clear - IC1 IC2 SZ Q1 Q4; lia|]. clear - Q2 IC1; Z.div_mod_to_equations; lia. }
      pose proof NG2 as NGc. unfold ng_cells in NGc.
      hide HD2. hide FR2. hide HPV2. hide BUF2. hide HEB2. hide NG2. hide AR1.
      (* [comment removed for export] *)
      step. rewrite (and3_aligned (B + idb_off)) by (clear - BI4 BIR; lia). step. if_false.
      (* [comment removed for export] *)
      step. rewrite (sx32_small (ng_ifcount sg)) by lia.
      step. clear NGc.
      step. step. replace (ng_ifcount sg + -1)%Z with (ng_ifcount sg - 1)%Z by lia.
      step.
      step. rewrite (unsigned_lit (ng_ifcount sg - 1)), Z.shiftl_mul_pow2 by lia. change (2 ^ 32)%Z with 4294967296%Z.
      step. rewrite (unsigned_lit ((ng_ifcount sg - 1) * 4294967296)) by (keep_hyps CEILV hptr sp R P B CUR EB lo idb_off p s c sg I' js hd SA pre0 IC1 IC2 SZ; nia). rewrite mulhu40 by lia.
      step. replace (I' + (ng_ifcount sg - 1) * 40)%Z with SA by lia.
      step. if_false_by (ltu_lits_false SA I' ltac:(clear - SAR Q1; lia) ltac:(clear - SAR Q1; lia)).
      step. rewrite (snez_pos I') by (clear - Q1 Q4 SZ; lia).
      step. rewrite (seqz_pos SA) by (clear - SAR Q1; lia).
      step. try replace (Z.lxor (bv_unsigned (Z_to_bv 64 1)) (bv_unsigned z64)) with 1%Z by reflexivity.
      step. if_false.
      step. if_false_by (eqz_false I' ltac:(clear - Q1 Q4 SZ; lia)).
      step. rewrite (and7_aligned SA) by (clear - SAR Q1; lia). step. if_false.
      (* [comment removed for export] *)
      step. rewrite (sx32_s32 (le4val x0 x1 x2 x3)) by (unfold le4val; lia).
      step. rewrite (and7_aligned CUR) by (clear - CUR1 CUR2 CUR8 RSP SP47; unfold rc_spmain in CUR2; lia).
      pose proof (munch_refl [(SA, SA + 4)]%Z m2) as MU2. pose proof (wmono_refl usegs m2) as WM2.
      step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m3 end.
      step. if_false.
      assert (AGS23 : agrees_on (fun a => outside [(SA, SA + 4)]%Z a) m2 m3) by (eapply agrees_on_of_munch; [exact MU2 | exact WM2 | intros a _ Ho; exact Ho]).
      unhide HD2. unhide FR2. unhide BUF2. unhide HEB2. unhide NG2. unhide AR1. clear HPV2.
      transport HD2 m3 AGS23 ltac:(prs). transport FR2 m3 AGS23 ltac:(prs). transport BUF2 m3 AGS23 ltac:((keep_hyps CEILV hptr sp R P B CUR EB lo idb_off p s c bs sg I' js hd SA pre0 IC2 HSA APIB SAR; prs)). transport HEB2 m3 AGS23 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo idb_off p s c ej m2 stG sg q1 I' js hd SA pre0 LO BU EBX IC2 HSA G2 APIP SAR; prs)).
      transport NG2 m3 AGS23 ltac:((keep_hyps CEILV hptr sp R P B CUR EB lo idb_off p s c sg I' js pad1 hd SA pre0 IC2 HSA APIP SAR; prs)).
      transport AR1 m3 AGS23 ltac:(intros a Ha; rewrite ifs_cells_size in Ha by (rewrite length_rev; lia); rewrite length_rev in Ha; cbn [outside]; lia).
      assert (G3 : GIo K R stG ((q1, I', 40 * ng_ifaces_size sg)%Z :: C1 ++ C2) FB m3).
      { eapply (GIo_client_frame K HFL SFL); [exact G2 | exact MU2 | exact WM2 |]. apply Forall_cons; [| apply Forall_nil]. right. unfold iv_in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
      rename ST2 into ST3.
      assert (AG3 : ai_AGP sp C1 C2 P B CUR EB p m m3).
      { eapply agrees_on_trans; [exact AG2|]. eapply agrees_on_weaken; [exact AGS23|]. intros a [[Ha|Ha] _]; cbn [outside]; (split; [| exact Logic.I]); [lia|].
        pose proof (CLB a Ha). destruct (proj1 (in_block_In _ _) Ha) as (b' & Hin & Hr). pose proof (head_apart K _ _ _ _ _ _ _ G2 Hin) as AP. cbn [cb_addr cb_size fst snd] in AP. (keep_hyps CEILV hptr sp R P B CUR EB lo idb_off p s sg I' js hd SA pre0 a b' IC2 HSA SAR Hr AP; lia). }
      clear MU2 WM2 AGS23 AG2 G2. rename MI2 into MI3.
      (* [comment removed for export] *)
      destruct (rw_cells_cut _ _ _ 2 JK') as [SL AR2]. clear JK'. cbn [firstn skipn cells_size csize Nat.add app] in SL, AR2.
      lazymatch type of AR2 with rw_cells _ _ ?A _ => replace A with (SA + 40)%Z in AR2 by lia end.
      lazymatch type of SL with rw_cells _ _ _ [_; CB 36 ?sjx] =>
        pose proof (rw_cells_recell _ _ _ [C4 (Z_to_bv 64 (ai_snap idb_off p)); CB 36 sjx] SL ltac:(pose proof (proj1 (proj1 SL)) as WF; cbn in WF |- *; clear - WF; (keep_hyps junk1 WF; tauto))
                      ltac:(cbn [cells_bytes cbytes app]; rewrite SNAP, le4_lit, le4_s32_lit by (keep_hyps CEILV hptr sp R P B CUR EB idb_off p s I' js hd SA x0 pre0 X0 x1 X1 x2 X2 x3 X3; lia); reflexivity)) as SL3 end.
      clear SL.
      (* [comment removed for export] *)
      step. step. step.
      lazymatch type of SL3 with rw_cells _ _ _ [_; CB 36 ?sjx] => lazymatch type of AR2 with rw_cells _ _ _ [CB _ ?tlx] =>
        assert (AIM0 : AIM K ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m R C1 C2 FB P B CUR EB lo idb_off p s c ej stG sg q1 I' SA js pad1 sjx tlx hd
                         (mkIdbOpts 1000000 0 false false false) c (pc_bufdata p) m3 bs cpad)
      end end.
      { split; [cbn; lia|]. split; [exact MI3|]. split; [exact ST3|]. split; [exact AG3|]. split; [exact HD2|]. split; [exact FR2|].
        split; [exact NG2|]. split; [exact AR1|]. split; [exact SL3|]. split; [exact AR2|]. split; [exact G3|]. split; [exact BUF2|]. split; [exact PFX|].
        split; [reflexivity|]. split; [exact GRD|]. split; [exact CC2|]. split; [exact CREM|]. split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [exact HEB2|].
        rewrite COFF. clear - IDB4. Z.div_mod_to_equations; lia. }
      unfold process_idb_options.
      destruct (Z.eq_dec (cur_remaining c) 0) as [R0|R0].
      - (* [comment removed for export] *)
        rewrite (eqb_lits_eq _ _ R0). cbv iota. do 3 step.
        rewrite R0. change (Z.to_nat (0 / 4 + 1)) with 1%nat. rewrite pio_unfold. unfold pio_iter. rewrite R0. cbn [Z.eqb]. cbv iota.
        eapply (ai_done K HFL SFL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m R st C1 C2 FB P B CUR EB lo idb_off p s c bs ej
                  LO BU RSP SPW HinP HinB P14 APB UTS IFW LENB CUR1 CUR8 IDB0 COFF CREM CEND EBX CLB stG sg q1 I' SA js pad1 _ _ hd U1 U2 U5 IC1 IC2 SZ LJS HSA SNR Hhd OFG);
          [reflexivity | reflexivity | reflexivity | exact AIM0].
      - (* [comment removed for export] *)
        rewrite (eqb_lits_false (cur_remaining c) 0) by (keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo idb_off p s c stG sg q1 I' js hd SA m3 pre0 LENB IDB0 COFF CREM CEND R0; lia). cbv iota.
        do 18 step.
        replace (Z.to_nat (cur_remaining c / 4 + 1)) with (S (Z.to_nat (cur_remaining c / 4))) by lia.
        eapply (ai_enter K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m R st C1 C2 FB P B I CUR EB lo idb_off p s i c bs ej
                  G LO BU SPM TP ALN RSP SPW HinP HinB P14 B14 APB P5' HPVm UTS IFW WMB LENB CUR1 CUR2 CUR8 IDB0 COFF CREM CEND CBT EBX EB64 CLB INPc CRE EBiv
                  stG sg q1 I' SA js pad1 _ _ hd U1 U2 U5 IC1 IC2 SZ LJS HSA SNR Hhd OFG);
          [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact AIM0 | (keep_hyps CEILV hptr sp R P B CUR EB lo idb_off p s c sg I' js hd SA pre0; lia) | (keep_hyps CEILV hptr sp R P B CUR EB idb_off p s c I' js hd SA pre0 CREM R0; lia)]. }
    (* [comment removed for export] *)
    assert (IBF : forall q, i = Some q -> (0 < I /\ I + 40 * ng_ifaces_size s <= CEILZ /\ (P + 680 <= I \/ I + 40 * ng_ifaces_size s <= P) /\ (B + pc_bufalloc p <= I \/ I + 40 * ng_ifaces_size s <= B))%Z).
    { intros q ->. assert (HinI : In (q, I, (40 * ng_ifaces_size s)%Z) ((C1 ++ IBLK (Some q) I s ++ C2) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
      pose proof (GIo_block_ok K _ _ _ _ _ _ G HinI) as (I1 & I2 & I3 & I4 & _). cbn [cb_addr cb_size fst snd] in I1, I2, I3, I4.
      pose proof (mid_apart K _ _ _ _ _ _ _ _ G HinP) as AP1. pose proof (mid_apart K _ _ _ _ _ _ _ _ G HinB) as AP2. cbn [cb_addr cb_size fst snd] in AP1, AP2. unfold PCAP_NG_SF_TOTAL in AP1. lia. }
    (* [comment removed for export] *)
    step.
    destruct (Z.lt_ge_cases (ng_ifaces_size s) (ng_ifcount s + 1)) as [GROW|NOGROW].
    2:{ (* [comment removed for export] *)
      if_tf' true. rewrite (proj2 (Z.ltb_ge (ng_ifaces_size s) (ng_ifcount s + 1)) NOGROW).
      destruct i as [q|]; [| exfalso; lia].
      destruct HIF as (js & tail & LJS & AR & E1 & E2 & E3 & IFW0). destruct (IBF q eq_refl) as (I1 & I4 & API & ABI).
      apply evt_done. apply (implM_retb usegs). cbv beta iota.
      set (SG := mkNg (ng_user_tsresol s) (ng_max_blocksize s) (ng_ifcount s + 1) (ng_ifaces_size s) (ng_ifaces s)).
      lazymatch goal with |- implM _ ?mdl _ _ _ =>
        replace mdl with (mret (St:=PS) (ai_result idb_off p s c SG (Some q) (process_idb_options (pc_swapped p) c (pc_bufdata p))))
          by (unfold ai_result, ai_slot, ai_scale; subst SG; destruct (process_idb_options _ _ _) as [bb [mm|[oo cc]]]; [reflexivity|]; cbn;
              destruct (io_tsresol oo =? ng_user_tsresol s); [reflexivity|]; destruct (ng_user_tsresol s <? io_tsresol oo); destruct (io_is_binary oo); reflexivity) end.
      apply (implM_ret usegs).
      (* [comment removed for export] *)
      unhide HEB. unhide HBUF. unhide HCUR. unhide HD. unhide FRS.
      transport HEB m1 AGS1 ltac:((keep_hyps CEILV H hptr K sp R st C1 C2 FB P B I CUR EB lo idb_off p s ej q m1 js LO BU P14 EBX G1; prs)). transport HBUF m1 AGS1 ltac:((keep_hyps CEILV hptr sp R P B CUR EB lo idb_off p s bs js APB; prs)). transport HCUR m1 AGS1 ltac:(prs). transport HD m1 AGS1 ltac:(prs). transport FRS m1 AGS1 ltac:(prs). transport HPV m1 AGS1 ltac:(prs).
      apply T0 in AR; [| rewrite cells_size_app, ifs_cells_size by (rewrite length_rev; lia); rewrite length_rev; cbn [cells_size csize Nat.add]; lia].
      transport AR m1 AGS1 ltac:(intros a Ha; rewrite cells_size_app, ifs_cells_size in Ha by (rewrite length_rev; (keep_hyps CEILV hptr sp R P B I CUR EB lo idb_off p s js tail a LJS; lia)); rewrite length_rev in Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside]; (keep_hyps CEILV hptr sp R P B I CUR EB lo idb_off p s js a IFC API Ha; lia)).
      destruct (proj1 (rw_cells_app usegs m1 I _ _) AR) as [AR1 JK]. clear AR. rewrite ifs_cells_size in JK by (rewrite length_rev; lia). rewrite length_rev in JK.
      assert (AGa1 : ai_AGP sp C1 C2 P B CUR EB p m m1).
      { eapply agrees_on_trans; [exact AGa|]. eapply agrees_on_weaken; [exact AGS1|]. intros a (_ & Hn & _); cbn [outside]. unfold PCAP_PRIV_OFF, PCAP_NG_SF_TOTAL in Hn. (keep_hyps CEILV hptr sp R P B CUR EB idb_off p s js a Hn; lia). }
      assert (G1p : GIo K R st ((q, I, 40 * ng_ifaces_size s)%Z :: C1 ++ C2) FB m1).
      { eapply (GIo_perm K HPL); [exact G1|]. cbn [IBLK app]. apply Permutation_sym. apply Permutation_middle. }
      eapply (KED0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 st SG q I js pad tail);
        [reflexivity | reflexivity | reflexivity | cbn; lia | cbn; lia | cbn; lia | exact LJS | exact IFW0 | exact MI | exact ST | exact AGa1 | exact HD | reflexivity | exact FRS | exact HPV | exact HBUF | exact HCUR | exact HEB
        | unfold ng_cells; cbn [SG ng_user_tsresol ng_max_blocksize ng_ifcount ng_ifaces_size]; exact HNG
        | exact AR1
        | cbn [SG ng_ifcount ng_ifaces_size]; replace (ng_ifcount s + 1 - 1)%Z with (ng_ifcount s) by lia;
          lazymatch type of JK with rw_cells _ _ ?A _ => replace (I + 40 * ng_ifcount s)%Z with A by lia end; exact JK
        | exact G1p | reflexivity ]. }
    (* [comment removed for export] *)
    if_tf' false. rewrite (proj2 (Z.ltb_lt (ng_ifaces_size s) (ng_ifcount s + 1)) GROW).
    unhide HEB. unhide HBUF. unhide HCUR. unhide HD. unhide FRS.
    transport HEB m1 AGS1 ltac:((keep_hyps CEILV H hptr K sp R st C1 C2 FB P B I CUR EB lo idb_off p s i ej m1 LO BU P14 EBX G1; prs)). transport HBUF m1 AGS1 ltac:((keep_hyps CEILV hptr sp R P B CUR EB lo idb_off p s bs APB; prs)). transport HCUR m1 AGS1 ltac:(prs). transport HD m1 AGS1 ltac:(prs). transport FRS m1 AGS1 ltac:(prs). transport HPV m1 AGS1 ltac:(prs).
    assert (AGa1 : ai_AGP sp C1 C2 P B CUR EB p m m1).
    { eapply agrees_on_trans; [exact AGa|]. eapply agrees_on_weaken; [exact AGS1|]. intros a (_ & Hn & _); cbn [outside]. unfold PCAP_PRIV_OFF, PCAP_NG_SF_TOTAL in Hn. lia. }
    pose proof (ai_snp K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m R st C1 C2 FB P B CUR EB lo idb_off p s c bs ej
                  LO BU SPM TP ALN RSP SPW HinP P14 B14 APB LENB CUR1 CUR2 CUR8 IDB0 COFF CREM CEND EBX CLB CRE EBiv) as SNP.
    hide HEB. hide HBUF. hide HCUR. hide HD. hide FRS.
    step.
    destruct (Z.eq_dec (ng_ifaces_size s) 0) as [SZ0|SZ0].
    - (* [comment removed for export] *)
      rewrite (eqb_lits_eq _ _ SZ0). cbv iota. rewrite (proj2 (Z.eqb_eq _ _) SZ0).
      destruct i as [q|]; [destruct HIF as (js & tail & LJS & AR & E1 & E2 & E3 & IFW0); exfalso; lia|]. destruct HIF as (I0 & IFN & IC0 & _).
      do 5 step.
      apply evt_done. apply (implM_bind_assoc usegs).
      name_sp sp (-112)%Z.
      eapply (implM_bind usegs).
      { eapply MALLOCS; [| reflexivity | unfold PCAP_NG_IF_SIZE; lia].
        split; [exact G1|]. split; [rewrite Hsp; exact ST|]. split; [unfold rc_lo; lia|]. split; [unfold MALLOC_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      intros qo st1 ms1 PO. cbv beta in PO.
      destruct PO as (av & m2 & E & OF1 & MI2 & ST2 & AG12 & RM).
      unfold hpost_regs in E. destruct_exs E. subst ms1. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 95704)) with (Z_to_bv 64 95704) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      cbn [IBLK app] in AG12.
      unhide HEB. unhide HBUF. unhide HCUR. unhide HD. unhide FRS.
      transport HD m2 AG12 ltac:(prs). transport FRS m2 AG12 ltac:(prs). transport HPV m2 AG12 ltac:((keep_hyps CEILV hptr sp R C1 C2 P B CUR EB idb_off p s INPc; prs)). transport HNG m2 AG12 ltac:((keep_hyps CEILV hptr sp R C1 C2 P B I CUR EB idb_off p s pad INPc; prs)).
      transport HBUF m2 AG12 ltac:(prs). transport HCUR m2 AG12 ltac:(prs). transport HEB m2 AG12 ltac:((keep_hyps CEILV hptr sp R C1 C2 P B CUR EB lo idb_off p s ej INPc EBX; prs)).
      assert (AGa2 : ai_AGP sp C1 C2 P B CUR EB p m m2).
      { eapply agrees_on_trans; [exact AGa1|]. eapply agrees_on_weaken; [exact AG12|]. intros a ([Ha|Ha] & _); [left; lia| right; exact Ha]. }
      clear AG12 MI ST.
      hide HEB. hide HBUF. hide HCUR. hide HD. hide FRS. hide HPV.
      destruct qo as [q'|].
      + (* [comment removed for export] *)
        destruct RM as (A & junkA & -> & G2 & HBK). cbn [IBLK app] in G2.
        pose proof (GIo_block_ok K _ _ _ _ _ _ G2 ltac:(left; reflexivity)) as (Q1 & Q2 & Q3 & Q4 & _). cbn [cb_addr cb_size fst snd] in Q1, Q2, Q3, Q4. unfold PCAP_NG_IF_SIZE in Q4, HBK.
        pose proof (head_apart K _ _ _ _ _ _ _ G2 HinP) as APIP. cbn [cb_addr cb_size fst snd] in APIP. unfold PCAP_NG_SF_TOTAL, PCAP_NG_IF_SIZE in APIP.
        (* [comment removed for export] *)
        cbv iota. apply (implM_retb usegs). cbv beta iota.
        set (SG := mkNg (ng_user_tsresol s) (ng_max_blocksize s) (ng_ifcount s + 1) 1 (ng_ifaces s)).
        lazymatch goal with |- implM _ ?mdl _ _ _ =>
          replace mdl with (mret (St:=PS) (ai_result idb_off p s c SG (Some q') (process_idb_options (pc_swapped p) c (pc_bufdata p))))
            by (unfold ai_result, ai_slot, ai_scale; subst SG; destruct (process_idb_options _ _ _) as [bb [mm|[oo cc]]]; [reflexivity|]; cbn;
                destruct (io_tsresol oo =? ng_user_tsresol s); [reflexivity|]; destruct (ng_user_tsresol s <? io_tsresol oo); destruct (io_is_binary oo); reflexivity) end.
        apply (implM_ret usegs).
        step. step. step. rewrite (eqb_lits_false A 0) by lia. cbv iota.
        step. step. step.
        pose proof (munch_refl [(P + 664, P + 668); (P + 672, P + 680)]%Z m2) as MU3. pose proof (wmono_refl usegs m2) as WM3.
        hide HBK.
        step. step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m3 end.
        assert (AGS23 : agrees_on (fun a => outside [(P + 664, P + 668); (P + 672, P + 680)]%Z a) m2 m3) by (eapply agrees_on_of_munch; [exact MU3 | exact WM3 | intros a _ Ho; exact Ho]).
        assert (G3 : GIo K R st1 ((q', A, 40)%Z :: C1 ++ C2) FB m3).
        { eapply (GIo_client_frame K HFL SFL); [exact G2 | exact MU3 | exact WM3 |].
          apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; right; unfold iv_in_block; apply Exists_cons_tl; apply Exists_exists;
            exists (pc_self p, P, PCAP_NG_SF_TOTAL); (split; [exact HinP|]); cbn [cb_addr cb_size fst snd]; unfold PCAP_NG_SF_TOTAL; lia. }
        unhide HEB. unhide HBUF. unhide HCUR. unhide HD. unhide FRS. unhide HPV. unhide HBK.
        transport HD m3 AGS23 ltac:(prs). transport FRS m3 AGS23 ltac:(prs). transport HPV m3 AGS23 ltac:(prs).
        transport HBUF m3 AGS23 ltac:((keep_hyps CEILV hptr sp R P B CUR EB lo idb_off p s c bs A APB; prs)). transport HCUR m3 AGS23 ltac:(prs). transport HEB m3 AGS23 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo idb_off p s ej q' st1 A m3 LO BU P14 EBX G3; prs)). transport HBK m3 AGS23 ltac:((keep_hyps CEILV hptr sp R P B CUR EB lo idb_off p s A junkA APIP; prs)).
        assert (AGa3 : ai_AGP sp C1 C2 P B CUR EB p m m3).
        { eapply agrees_on_trans; [exact AGa2|]. eapply agrees_on_weaken; [exact AGS23|]. intros a (_ & Hn & _); cbn [outside]. unfold PCAP_PRIV_OFF, PCAP_NG_SF_TOTAL in Hn. lia. }
        clear MU3 WM3 AGS23 G2 AGa2.
        destruct (rw_cells_cut _ _ _ 0 HBK) as [AR1 _]. cbn [firstn] in AR1.
        eapply (KED0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 st1 SG q' A [] pad junkA);
          [reflexivity | reflexivity | reflexivity | cbn; rewrite IFN; cbn; lia | cbn; lia | cbn; lia | rewrite IFN; reflexivity | rewrite IFN; constructor | exact MI2 | exact ST2 | exact AGa3 | exact HD | reflexivity | exact FRS | exact HPV | exact HBUF | exact HCUR | exact HEB
          | unfold ng_cells; cbn [SG ng_user_tsresol ng_max_blocksize ng_ifcount ng_ifaces_size]; exact HNG
          | rewrite IFN; cbn [rev ifs_cells]; exact AR1
          | cbn [SG ng_ifcount ng_ifaces_size]; replace (A + 40 * (ng_ifcount s + 1 - 1))%Z with A by lia; replace (Z.to_nat (40 * (1 - (ng_ifcount s + 1 - 1)))) with (Z.to_nat 40) by lia; exact HBK
          | exact G3 | exact OF1 ].
      + (* [comment removed for export] *)
        destruct RM as (-> & G2 & _). cbn [IBLK app] in G2.
        cbv iota. apply (implM_retb usegs). cbv beta iota. apply (implM_ret usegs).
        step. step. step. rewrite (eqb_lits_eq 0 0 eq_refl). cbv iota.
        step. change (sx32 (Z_to_bv 64 (ng_ifcount s + 1))) with (sx32 (Z_to_bv 64 (ng_ifcount s + 1))). rewrite (sx32_small (ng_ifcount s + 1)) by lia.
        do 4 step.
        unhide HEB. unhide HBUF. unhide HCUR. unhide HD. unhide FRS. unhide HPV.
        assert (MSG : fmt_at m2 AI_FMT_OOM_IF "out of memory for per-interface information (%u interfaces)"%string)
          by (apply (fmt_at_intro m2 _ _ MI2); [vm_compute; reflexivity| unfold AI_FMT_OOM_IF; lia| unfold AI_FMT_OOM_IF; cbn; lia]).
        eapply SNP with (m3:=m2) (args:=[AInt (ng_ifcount s + 1)]);
          [ exact MI2 | exact ST2 | exact AGa2 | exact HD | reflexivity | exact FRS | exact HEB | exact MSG | reflexivity | cbn; lia
          | intros; cbn [length firstn]; apply Forall2_cons; [reflexivity| apply Forall2_nil] | unfold Msg.oom_interfaces, PCAP_ERRBUF_SIZE; reflexivity | vm_compute; reflexivity | apply args_ok_ints1 | ].
        exists (mkNg (ng_user_tsresol s) (ng_max_blocksize s) (ng_ifcount s + 1) (ng_ifaces_size s) (ng_ifaces s)), None, I, pad, bs.
        split; [exact OF1|]. split; [reflexivity|]. split; [cbn [IBLK app]; exact G2|]. split; [unfold ng_cells; cbn; exact HNG|]. split; [reflexivity|]. split; [reflexivity|]. split; [cbn; lia|]. split; [cbn; lia|].
        split; [exact HBUF|]. split; [exact PFX|]. split; [reflexivity|]. split; [exact GRD|]. split; [exact I0|].
        eexists. split; [exact HCUR| reflexivity].
    - (* [comment removed for export] *)
      rewrite (eqb_lits_false (ng_ifaces_size s) 0) by lia. cbv iota. rewrite (proj2 (Z.eqb_neq _ _) SZ0). cbv iota.
      (* [comment removed for export] *)
      destruct (Z.lt_ge_cases (ng_ifcount s) (2 ^ 22)) as [IFC25|IFC25].
      2:{ replace (ng_ifcount s <? 2 ^ 22) with false by (symmetry; apply Z.ltb_ge; exact IFC25). cbv beta iota delta [negb].
          apply evt_done. apply (implM_unr usegs st). }
      replace (ng_ifcount s <? 2 ^ 22) with true by (symmetry; apply Z.ltb_lt; exact IFC25). cbv beta iota delta [negb].
      destruct i as [q|]; [| destruct HIF as (_ & _ & _ & E0); exfalso; lia].
      destruct HIF as (js & tail & LJS & AR & E1 & E2 & E3 & IFW0). destruct (IBF q eq_refl) as (I1 & I4 & API & ABI).
      assert (SZE : ng_ifaces_size s = ng_ifcount s) by lia.
      step. if_tf' false.
      step. rewrite (unsigned_lit (ng_ifaces_size s)), Z.shiftl_mul_pow2 by lia. change (2 ^ 1)%Z with 2%Z.
      step. step. rewrite (unsigned_lit (ng_ifaces_size s * 2)), Z.shiftl_mul_pow2 by lia. change (2 ^ 32)%Z with 4294967296%Z.
      step. step. rewrite (unsigned_lit (ng_ifaces_size s * 2 * 4294967296)), Z.shiftr_div_pow2 by lia. change (2 ^ 32)%Z with 4294967296%Z. rewrite Z.div_mul by lia.
      step. rewrite (unsigned_lit (ng_ifaces_size s * 2 * 4294967296)) by lia. rewrite mulhu40 by lia.
      step. if_tf' true.
      (* [comment removed for export] *)
      apply T0 in AR; [| rewrite cells_size_app, ifs_cells_size by (rewrite length_rev; lia); rewrite length_rev; cbn [cells_size csize Nat.add]; lia].
      transport AR m1 AGS1 ltac:(intros a Ha; rewrite cells_size_app, ifs_cells_size in Ha by (rewrite length_rev; (keep_hyps CEILV hptr sp R P B I CUR EB lo idb_off p s js tail a LJS; lia)); rewrite length_rev in Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside]; (keep_hyps CEILV hptr sp R P B I CUR EB lo idb_off p s js a IFC API Ha; lia)).
      pose proof (proj1 (proj1 AR)) as WFA. apply cells_wf_app in WFA as [WFI WFT]. cbn in WFT. destruct WFT as [LT _].
      assert (TL0 : tail = []) by (destruct tail; [reflexivity| cbn in LT; lia]). subst tail.
      assert (ARm : rw_cells usegs m1 I ([] ++ (ifs_cells (rev (ng_ifaces s)) js ++ [CB (Z.to_nat (40 * (ng_ifaces_size s - ng_ifcount s))) []]) ++ [])) by (cbn [app]; rewrite app_nil_r; exact AR).
      apply rw_cells_merge in ARm. cbn [app] in ARm. rewrite cells_size_app, cells_bytes_app, ifs_cells_size in ARm by (rewrite length_rev; lia). rewrite length_rev in ARm.
      cbn [cells_size cells_bytes cbytes csize Nat.add app] in ARm. rewrite app_nil_r in ARm.
      replace (40 * length (ng_ifaces s) + (Z.to_nat (40 * (ng_ifaces_size s - ng_ifcount s)) + 0))%nat with (Z.to_nat (40 * ng_ifaces_size s)) in ARm by lia.
      (* [comment removed for export] *)
      do 6 step.
      apply evt_done. apply (implM_bind_assoc usegs).
      name_sp sp (-112)%Z.
      cbn [IBLK app] in G1.
      eapply (implM_bind usegs).
      { eapply REALLOC; [| reflexivity | unfold PCAP_NG_IF_SIZE; reflexivity | unfold PCAP_NG_IF_SIZE; lia | exact ARm].
        split; [exact G1|]. split; [rewrite Hsp; exact ST|]. split; [unfold rc_lo; lia|]. split; [unfold MALLOC_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      intros qo st1 ms1 PO. cbv beta in PO.
      destruct PO as (av & m2 & E & OF1 & MI2 & ST2 & AG12 & RM).
      unfold hpost_regs in E. destruct_exs E. subst ms1. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 96464)) with (Z_to_bv 64 96464) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      unhide HEB. unhide HBUF. unhide HCUR. unhide HD. unhide FRS.
      transport HD m2 AG12 ltac:(prs). transport FRS m2 AG12 ltac:(prs). transport HPV m2 AG12 ltac:((keep_hyps CEILV hptr sp R C1 C2 P B CUR EB idb_off p s js INPc; prs)). transport HNG m2 AG12 ltac:((keep_hyps CEILV hptr sp R C1 C2 P B I CUR EB idb_off p s pad js INPc; prs)).
      transport HBUF m2 AG12 ltac:((keep_hyps CEILV hptr sp R C1 C2 P B CUR EB lo idb_off p s c bs js INBc; prs)). transport HCUR m2 AG12 ltac:(prs). transport HEB m2 AG12 ltac:((keep_hyps CEILV hptr sp R C1 C2 P B CUR EB lo idb_off p s ej js INPc EBX; prs)).
      assert (AGa2 : ai_AGP sp C1 C2 P B CUR EB p m m2).
      { eapply agrees_on_trans; [exact AGa1|]. eapply agrees_on_weaken; [exact AG12|]. intros a ([Ha|Ha] & _); [left; lia| right; exact Ha]. }
      clear AG12 MI ST AR ARm.
      hide HEB. hide HBUF. hide HCUR. hide HD. hide FRS. hide HPV.
      unfold PCAP_NG_IF_SIZE in RM.
      destruct qo as [q'|].
      + (* [comment removed for export] *)
        destruct RM as (A & junkA & -> & G2 & HBK).
        pose proof (GIo_block_ok K _ _ _ _ _ _ G2 ltac:(left; reflexivity)) as (Q1 & Q2 & Q3 & Q4 & _). cbn [cb_addr cb_size fst snd] in Q1, Q2, Q3, Q4.
        pose proof (head_apart K _ _ _ _ _ _ _ G2 HinP) as APIP. cbn [cb_addr cb_size fst snd] in APIP. unfold PCAP_NG_SF_TOTAL in APIP.
        rewrite !Z.min_l in HBK by lia.
        (* [comment removed for export] *)
        cbv iota. apply (implM_retb usegs). cbv beta iota.
        set (SG := mkNg (ng_user_tsresol s) (ng_max_blocksize s) (ng_ifcount s + 1) (ng_ifaces_size s * 2) (ng_ifaces s)).
        lazymatch goal with |- implM _ ?mdl _ _ _ =>
          replace mdl with (mret (St:=PS) (ai_result idb_off p s c SG (Some q') (process_idb_options (pc_swapped p) c (pc_bufdata p))))
            by (unfold ai_result, ai_slot, ai_scale; subst SG; destruct (process_idb_options _ _ _) as [bb [mm|[oo cc]]]; [reflexivity|]; cbn;
                destruct (io_tsresol oo =? ng_user_tsresol s); [reflexivity|]; destruct (ng_user_tsresol s <? io_tsresol oo); destruct (io_is_binary oo); reflexivity) end.
        apply (implM_ret usegs).
        step. step. rewrite (eqb_lits_false A 0) by lia. cbv beta iota delta [negb].
        step. step. step.
        pose proof (munch_refl [(P + 664, P + 668); (P + 672, P + 680)]%Z m2) as MU3. pose proof (wmono_refl usegs m2) as WM3.
        hide HBK.
        step. step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m3 end.
        assert (AGS23 : agrees_on (fun a => outside [(P + 664, P + 668); (P + 672, P + 680)]%Z a) m2 m3) by (eapply agrees_on_of_munch; [exact MU3 | exact WM3 | intros a _ Ho; exact Ho]).
        assert (G3 : GIo K R st1 ((q', A, ng_ifaces_size s * 2 * 40)%Z :: C1 ++ C2) FB m3).
        { eapply (GIo_client_frame K HFL SFL); [exact G2 | exact MU3 | exact WM3 |].
          apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; right; unfold iv_in_block; apply Exists_cons_tl; apply Exists_exists;
            exists (pc_self p, P, PCAP_NG_SF_TOTAL); (split; [exact HinP|]); cbn [cb_addr cb_size fst snd]; unfold PCAP_NG_SF_TOTAL; lia. }
        unhide HEB. unhide HBUF. unhide HCUR. unhide HD. unhide FRS. unhide HPV. unhide HBK.
        transport HD m3 AGS23 ltac:(prs). transport FRS m3 AGS23 ltac:(prs). transport HPV m3 AGS23 ltac:(prs).
        transport HBUF m3 AGS23 ltac:((keep_hyps CEILV hptr sp R P B CUR EB lo idb_off p s c bs js A APB; prs)). transport HCUR m3 AGS23 ltac:(prs). transport HEB m3 AGS23 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo idb_off p s ej js q' st1 A m3 LO BU P14 EBX G3; prs)). transport HBK m3 AGS23 ltac:((keep_hyps CEILV hptr sp R P B CUR EB lo idb_off p s js A junkA APIP; prs)).
        assert (AGa3 : ai_AGP sp C1 C2 P B CUR EB p m m3).
        { eapply agrees_on_trans; [exact AGa2|]. eapply agrees_on_weaken; [exact AGS23|]. intros a (_ & Hn & _); cbn [outside]. unfold PCAP_PRIV_OFF, PCAP_NG_SF_TOTAL in Hn. (keep_hyps CEILV hptr sp R P B CUR EB idb_off p s js A a Hn; lia). }
        clear MU3 WM3 AGS23 G2 AGa2.
        (* [comment removed for export] *)
        destruct (rw_cells_cut _ _ _ 1 HBK) as [AR1 JK]. cbn [firstn skipn cells_size csize Nat.add] in AR1, JK.
        pose proof (rw_cells_recell _ _ _ (ifs_cells (rev (ng_ifaces s)) js) AR1 WFI
                      ltac:(cbn [cells_bytes cbytes app]; rewrite app_nil_r; symmetry; apply firstn_all2; rewrite (cells_bytes_length _ WFI), ifs_cells_size by (rewrite length_rev; lia); rewrite length_rev; lia)) as AR1'.
        eapply (KED0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 st1 SG q' A js pad junkA);
          [reflexivity | reflexivity | reflexivity | cbn; (keep_hyps CEILV hptr sp R P B CUR EB lo idb_off p s js A E1; lia) | cbn; (keep_hyps CEILV hptr sp R P B CUR EB lo idb_off p s js A E3 SZE; lia) | cbn; (keep_hyps CEILV hptr sp R P B CUR EB lo idb_off p s js A E3 IFC25 SZE; lia) | exact LJS | exact IFW0 | exact MI2 | exact ST2 | exact AGa3 | exact HD | reflexivity | exact FRS | exact HPV | exact HBUF | exact HCUR | exact HEB
          | unfold ng_cells; cbn [SG ng_user_tsresol ng_max_blocksize ng_ifcount ng_ifaces_size]; exact HNG
          | exact AR1'
          | cbn [SG ng_ifcount ng_ifaces_size]; lazymatch type of JK with rw_cells _ _ ?AA [CB ?n _] => replace (A + 40 * (ng_ifcount s + 1 - 1))%Z with AA by (keep_hyps CEILV hptr sp R P B CUR EB lo idb_off p s js A E3 SZE; lia); replace (Z.to_nat (40 * (ng_ifaces_size s * 2 - (ng_ifcount s + 1 - 1)))) with n by (keep_hyps CEILV hptr sp R P B CUR EB lo idb_off p s js A SZE; lia) end; exact JK
          | replace (40 * ng_ifaces_size SG)%Z with (ng_ifaces_size s * 2 * 40)%Z by (cbn [SG ng_ifaces_size]; (keep_hyps CEILV hptr sp R P B CUR EB idb_off p s js A; lia)); exact G3 | exact OF1 ].
      + (* [comment removed for export] *)
        destruct RM as (-> & G2 & HBK & _).
        cbv iota. apply (implM_retb usegs). cbv beta iota. apply (implM_ret usegs).
        step. step. rewrite (eqb_lits_eq 0 0 eq_refl). cbv beta iota delta [negb].
        step. change (sx32 (Z_to_bv 64 (ng_ifcount s + 1))) with (sx32 (Z_to_bv 64 (ng_ifcount s + 1))). rewrite (sx32_small (ng_ifcount s + 1)) by lia.
        do 4 step.
        unhide HEB. unhide HBUF. unhide HCUR. unhide HD. unhide FRS. unhide HPV.
        assert (MSG : fmt_at m2 AI_FMT_OOM_IF "out of memory for per-interface information (%u interfaces)"%string)
          by (apply (fmt_at_intro m2 _ _ MI2); [vm_compute; reflexivity| unfold AI_FMT_OOM_IF; lia| unfold AI_FMT_OOM_IF; cbn; lia]).
        eapply SNP with (m3:=m2) (args:=[AInt (ng_ifcount s + 1)]);
          [ exact MI2 | exact ST2 | exact AGa2 | exact HD | reflexivity | exact FRS | exact HEB | exact MSG | reflexivity | cbn; lia
          | intros; cbn [length firstn]; apply Forall2_cons; [reflexivity| apply Forall2_nil] | unfold Msg.oom_interfaces, PCAP_ERRBUF_SIZE; reflexivity | vm_compute; reflexivity | apply args_ok_ints1 | ].
        exists (mkNg (ng_user_tsresol s) (ng_max_blocksize s) (ng_ifcount s + 1) (ng_ifaces_size s) (ng_ifaces s)), (Some q), I, pad, bs.
        split; [exact OF1|]. split; [reflexivity|]. split; [cbn [IBLK app ng_ifaces_size]; eapply (GIo_perm K HPL); [exact G2| apply Permutation_sym; apply Permutation_middle]|].
        split; [unfold ng_cells; cbn; exact HNG|]. split; [reflexivity|]. split; [reflexivity|]. split; [cbn; lia|]. split; [cbn; lia|].
        split; [exact HBUF|]. split; [exact PFX|]. split; [reflexivity|]. split; [exact GRD|].
        split. { unfold ng_ifaces_closable. cbn [ng_ifaces_size]. split; [eexists; exact HBK| lia]. }
        eexists. split; [exact HCUR| reflexivity].
  Qed.
  End Sz3.
  Theorem add_interface_proof : ltac:(let t := eval cbv delta [add_interface_proof__stmt] in add_interface_proof__stmt in exact t).
  Proof using HFL HPL MALLOCS REALLOC SFL SNPRINTF. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R st C1 C2 FB P B I CUR EB lo idb_off p s i c bs ej pad cpad. ltac2:(SecDiet.SzSec.closeP 'add_interface_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End AI.

End WithCeil.
End F_sfpcapng_ai.

(* [comment removed for export] *)
Module F_sfpcapng_chkC.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep MonadX Image ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pcap_err__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface_ng.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_small.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_open.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_fopen.TwB. 
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3 Require F_sfpcap_chkF__U3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3.F_sfpcap_chkF__U3.F_sfpcapng_chkK. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pcap_err__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcap_chkA__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_aiE__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_sfpcapng_chkA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_chkF.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_chkB.TwB.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Ubsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac gio_ceil_fact :=
  match goal with
  | G : GIo _ _ _ _ _ _ |- _ => let H := fresh "CLO__" in pose proof (S3.PcapRep.TwB.GIo_ceil_lo _ _ _ _ _ _ G) as H; unfold rc_lo in H
  end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try gio_ceil_fact; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)

Section WithCeil.
Context {CEILV : CEIL}.
Lemma swap4_at pre (u0 u1 u2 u3 : Z) rest :
  swap_field 4 (Z.of_nat (length pre)) (pre ++ u0 :: u1 :: u2 :: u3 :: rest) = pre ++ u3 :: u2 :: u1 :: u0 :: rest.
Proof using Type. pin_using tt.
  unfold swap_field.
  replace (zslice (Z.of_nat (length pre)) 4 (pre ++ u0 :: u1 :: u2 :: u3 :: rest)) with [u0; u1; u2; u3] by (symmetry; exact (zslice_at pre [u0; u1; u2; u3] rest)).
  unfold buf_write_at, zfirstn, zskipn, zlength. cbn [rev app length].
  rewrite Nat2Z.id, firstn_app, Nat.sub_diag, firstn_all. cbn [firstn]. rewrite app_nil_r.
  replace (Z.to_nat (Z.of_nat (length pre) + Z.of_nat 4)) with (length pre + 4)%nat by lia.
  rewrite skipn_app, skipn_all2 by lia. replace (length pre + 4 - length pre)%nat with 4%nat by lia. reflexivity.
Qed.
End WithCeil.


Open Scope bv_scope.

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Definition idb_swap_block__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (A : Z) (l0 l1 r0 r1 n0 n1 n2 n3 : Z),
    mem_inv usegs m -> (0 < A)%Z -> (A + 8 < 2^64)%Z ->
    (0 <= l0 < 256)%Z -> (0 <= l1 < 256)%Z -> (0 <= r0 < 256)%Z -> (0 <= r1 < 256)%Z ->
    (0 <= n0 < 256)%Z -> (0 <= n1 < 256)%Z -> (0 <= n2 < 256)%Z -> (0 <= n3 < 256)%Z ->
    s2 = Z_to_bv 64 A ->
    rw_cells usegs m A [C2 (Z_to_bv 64 (l0 + 256 * l1)); C2 (Z_to_bv 64 (r0 + 256 * r1)); C4 (Z_to_bv 64 (le4val n0 n1 n2 n3))] ->
    evt usegs (fun ms' => exists (a1' a2' a3' a4' a5' : word) m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x16f08) fc None m' (seg_rom usegs)
        /\ munch [(A, A + 8)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
        /\ rw_cells usegs m' A [C2 (Z_to_bv 64 (l1 + 256 * l0)); C2 (Z_to_bv 64 (r0 + 256 * r1)); C4 (Z_to_bv 64 (le4val n3 n2 n1 n0))])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x16ec0) fc None m (seg_rom usegs)).
Section Sz1.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A l0 l1 r0 r1 n0 n1 n2 n3 : ltac2:(SecDiet.SzSec.tyM 'idb_swap_block__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma idb_swap_block__body : ltac2:(SecDiet.SzSec.bodyP 'idb_swap_block__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt.
 intros MI HA1 HA2 L0 L1 R0 R1 N0 N1 N2 N3 -> HC.
  pose proof (munch_refl [(A, A + 8)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  do 18 step.
  apply evt_done. do 6 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  eapply rw_cells_recell; [exact HC | cbn; repeat split; exact Logic.I |].
  cbn [cells_bytes cbytes app].
  rewrite (le2_lit l1 l0), (le2_lit r0 r1), (le4_lit n3 n2 n1 n0) by lia.
  rewrite (le2_of_val _ l1 l0 l1); [| lia | lia | lia | apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.swap16_val; [lia | lia | apply unsigned_zx16; lia] ].
  rewrite (le4_of_val _ n3 n2 n1 n0 (n1 + 256 * n2 + 65536 * n3 + 16777216 * ((((n3 / 128) * 4294967295) mod 256))));
    [reflexivity | lia | lia | lia | lia | Z.div_mod_to_equations; lia
    | apply (swap32_val _ n0 n1 n2 n3); [lia|lia|lia|lia| Z.div_mod_to_equations; lia | rewrite unsigned_sx32 by lia; unfold sxv, le4val; lia]].
Qed.
End Sz1.
Lemma idb_swap_block : ltac:(let t := eval cbv delta [idb_swap_block__stmt] in idb_swap_block__stmt in exact t).
Proof using Type. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A l0 l1 r0 r1 n0 n1 n2 n3. ltac2:(SecDiet.SzSec.closeP 'idb_swap_block__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End WithCeil.


Close Scope bv_scope.

(* [comment removed for export] *)
Ltac prsMG GL := intros a Ha; rewrite cells_size_map_C1, GL in Ha; cbn [outside]; repeat match goal with |- _ /\ _ => split end; fastfirst (first [lia | left; lia | exact Logic.I]).

Section WithCeil.
Context {CEILV : CEIL}.
Section ChkNgC.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation PS := (PState H hptr).
  #[local] Notation pcapT := (PcapTypes.pcap hptr hptr).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis FREE : free_stmt_o HO K.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (lo MG FA EB ERR : Z) (f : hptr) (magic : list Z).
  Hypothesis CTX : ngc_ctx K sites sp tp R s CL FB lo MG FA EB ERR f magic m.
  #[local] Notation POSTQ := (check_header_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL FB lo MG EB ERR magic f m (ps_outfile s)).
  #[local] Notation AGQ := (ngc_AGQ sp CL EB ERR m).
  #[local] Notation FRS := (ngc_FRS ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9).
  #[local] Notation PR := (prims HO fo_nop sites).
  (* [comment removed for export] *)
  Variables (qs : hptr) (P : Z) (sw : bool) (BS0 MINOR : Z) (ew : word).
  Hypothesis P14 : 0 < P /\ P + 680 <= CEILZ.
  Hypothesis P16 : P mod 16 = 0.
  Hypothesis P5 : out_of_image P 680.
  Hypothesis BS0R : 1 <= BS0 <= 2^21.
  Hypothesis MINR : 0 <= MINOR < 2^16.

  #[local] Notation pL := (ngc_p f qs sw BS0 MINOR).
  #[local] Notation hcells := (ngc_hcells P sw BS0 MINOR).

  Open Scope bv_scope.

  (* [comment removed for export] *)
  Definition ngc_snp_fail__stmt : Prop := forall (t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' a3v a4v x2 x4 x5 x7 x9 : word) (RA : Z) (m3 : mem) (ps3 : PS)
           (fs : string) (args : list farg) (FMTA : Z) (msg bufdata : list Z)
           (qb : hptr) (i : option hptr) (sg : pcap_ng_sf) (B I nb : Z) (e : list byte) (hc : list cell),
      (RA = 0x16fec)%Z ->
      mem_inv usegs m3 -> stk usegs m3 lo (bv_unsigned sp + -128) -> AGQ m3 ->
      GIo K R ps3 (IBLK i I sg ++ (qs, P, 680%Z) :: (qb, B, nb) :: CL) FB m3 -> ps_outfile ps3 = ps_outfile s ->
      match i with Some _ => True | None => I = 0%Z end ->
      rw_cells usegs m3 (bv_unsigned sp + -128) hc -> cells_size hc = 40%nat -> FRS m3 ->
      rw_cells usegs m3 ERR [C4 ew] -> rw_cells usegs m3 MG (map (fun z => C1 (Z_to_bv 8 z)) magic) -> rw_cells usegs m3 EB [CB 256 e] ->
      rw_cells usegs m3 (P + 24) [C8 (Z_to_bv 64 B)] -> rw_cells usegs m3 (P + 672) [C8 (Z_to_bv 64 I)] ->
      (0 <= I < 2^64)%Z -> (1 <= nb)%Z ->
      fmt_at m3 FMTA fs -> fmt_ok fs args = true -> (length args <= 3)%nat ->
      (forall (CLx : list cblk) D dn, Forall2 (farg_word R CLx (bv_unsigned sp + -128) D dn m3) args (firstn (length args) [a3v; a4v; a5'])) ->
      items_okb (fmt fs) = true -> Forall arg_ok args -> Fmt.snprintf 256 fs args = msg ->
      implM usegs (ngc_fail MOps PR msg (ngc_p f qs sw BS0 MINOR qb nb bufdata sg i)) ps3 POSTQ
        (MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 ERR) (Z_to_bv 64 EB)
                 (Z_to_bv 64 EB) (Z_to_bv 64 256) (Z_to_bv 64 FMTA) a3v a4v a5' a6' a7'
                 x2 (Z_to_bv 64 P) x4 x5 (Z_to_bv 64 (P + 648)) x7 (Z_to_bv 64 1) x9 s10 s11 t3' t4' t5' t6')
            F (Z_to_bv 64 SNPRINTF_ENTRY) fc None m3 (seg_rom usegs)).
  Section Sz2.
  Variables t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' a3v a4v x2 x4 x5 x7 x9 RA m3 ps3 fs args FMTA msg bufdata qb i sg B I nb e hc : ltac2:(SecDiet.SzSec.tyM 'ngc_snp_fail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @t0').
  Lemma ngc_snp_fail__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_snp_fail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using CTX FREE HFL HPL P14 SFL SNPRINTF. pin_using (fun (CTX FREE HFL HPL P14 SFL SNPRINTF : unit) => tt).
 intros HRA MI3 ST3 AG3 G3 OF3 HI HC3 Hhc FRS3 ERR3 MG3 HEB3 HPB HPI IR NB FAT FOK ALEN FW FIT AOK EMSG.
    pose proof CTX as (G & LO & BU & SPM & TP & ALN & HinF & SITES & GL & GR & R1 & R2 & R3 & E1 & E2 & D1 & E4 & E8).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. pose proof (GIo_sp47 K _ _ _ _ _ G) as SP47. pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2^64)%Z in RSP.
    pose proof E2 as EBU. unfold rc_spmain in EBU.
    destruct P14 as [P1 P4].
    destruct (ngl_facts K HPL _ _ _ _ _ _ _ _ _ _ _ _ _ G3 NB) as ((B1 & B2 & B4) & APB & API & NPB).
    assert (CLB : forall a, in_block CL a -> (a < CEILZ)%Z).
    { intros a Ha. destruct (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _]. exact (proj2 Hc). }
    unfold ngc_fail. cbn [e_fenter e_fret fo_enter fo_ret fo_nop prims]. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_free prims free_opt ng_ifaces_ptr_of pc_buffer pc_self pc_priv ngc_p].
    unfold implM. iprefix.
    name_sp sp (-128)%Z.
    eapply evt_cut.
    { eapply (SNPRINTF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R ps3 (IBLK i I sg ++ (qs, P, 680%Z) :: (qb, B, nb) :: CL) FB lo EB 256%Z FMTA fs args e);
        [ split; [exact G3|]; split; [rewrite Hsp; exact ST3|]; split; [unfold rc_lo; lia|]; split; [unfold STDIO_STACK; rewrite Hsp; lia|];
          split; [rewrite Hsp; lia|]; split; [exact MI3|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]
        | reflexivity | reflexivity | reflexivity | lia | exact FAT | exact FOK | exact ALEN | rewrite Hsp; apply FW | exact HEB3
        | right; rewrite Hsp; lia ]. }
    cbv beta. intros ms' PO. destruct PO as (av4 & m4 & junk4 & E & MU4 & WM4 & MI4 & ST4 & -> & HEB4).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
    assert (AGS : agrees_on (fun a => outside [(bv_unsigned sp + -128 - STDIO_STACK, bv_unsigned sp + -128); (EB, EB + 256)]%Z a) m3 m4)
      by (eapply agrees_on_of_munch; [exact MU4 | exact WM4 | intros a _ Ho; exact Ho]).
    unfold STDIO_STACK in AGS, MU4.
    assert (G4 : GIo K R ps3 (IBLK i I sg ++ (qs, P, 680%Z) :: (qb, B, nb) :: CL) FB m4).
    { eapply (GIo_client_frame K HFL SFL); [exact G3 | exact MU4 | exact WM4 |].
      apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia|]. apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]. }
    transport HC3 m4 AGS ltac:(intros a Ha; rewrite Hhc in Ha; cbn [outside]; lia).
    unfold ngc_FRS in FRS3. transport FRS3 m4 AGS ltac:(prs). transport ERR3 m4 AGS ltac:(prs).
    transport MG3 m4 AGS ltac:(intros a Ha; rewrite cells_size_map_C1, GL in Ha; cbn [outside]; lia).
    transport HPB m4 AGS ltac:(prs). transport HPI m4 AGS ltac:(prs).
    assert (AG4 : AGQ m4).
    { unfold ngc_AGQ in AG3 |- *. eapply agrees_on_trans; [exact AG3|]. eapply agrees_on_weaken; [exact AGS|].
      intros a [[Ha|Ha] [Hn _]]; cbn [outside]; [lia|]. pose proof (CLB a Ha). lia. }
    pose proof (snprintf_length 256 fs args) as LS. change (Z.to_nat (256 - 1)) with 255%nat in LS. rewrite EMSG in LS, HEB4.
    change (Z.to_nat 256) with 256%nat in HEB4.
    replace (256 - length msg - 1)%nat with (255 - length msg)%nat in HEB4 by lia.
    hide HC3. hide FRS3. hide ERR3. hide MG3. hide HEB4. hide HPB. hide HPI.
    subst RA. replace (ret_pc (Z_to_bv 64 0x16fec)) with (Z_to_bv 64 0x16fec) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    all: step.
    all: unhide HC3; unhide FRS3; unhide ERR3; unhide MG3; unhide HEB4; unhide HPB; unhide HPI.
    all: apply evt_done; eapply (ngc_fail3 HO K sites HFL SFL FREE ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m) with (i := i) (ni := (40 * ng_ifaces_size sg)%Z);
      [ exact CTX | exact MI4 | exact ST4 | exact AG4 | destruct i; exact G4 | exact HI | exact HC3 | exact Hhc | exact FRS3 | exact ERR3 | exact MG3 | exact HEB4
      | lia | rewrite <- EMSG; apply snprintf_ok; [exact FIT| exact AOK] | exact OF3 | exact HPB | exact HPI | exact IR | lia | lia ].
  Qed.
  End Sz2.
  Lemma ngc_snp_fail : ltac:(let t := eval cbv delta [ngc_snp_fail__stmt] in ngc_snp_fail__stmt in exact t).
  Proof using CTX FREE HFL HPL P14 SFL SNPRINTF. intros t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' a3v a4v x2 x4 x5 x7 x9 RA m3 ps3 fs args FMTA msg bufdata qb i sg B I nb e hc. ltac2:(SecDiet.SzSec.closeP 'ngc_snp_fail__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ngc_mcp_fail__stmt : Prop := forall (ra' t0' t1' t2' a0' a3' a4' a5' a6' a7' t3' t4' t5' t6' x2 x4 x5 x7 x9 : word) (m3 : mem) (ps3 : PS)
           (SRC n : Z) (str : string) (msg bufdata : list Z)
           (qb : hptr) (i : option hptr) (sg : pcap_ng_sf) (B I nb : Z) (e : list byte) (hc : list cell),
      mem_inv usegs m3 -> stk usegs m3 lo (bv_unsigned sp + -128) -> AGQ m3 ->
      GIo K R ps3 (IBLK i I sg ++ (qs, P, 680%Z) :: (qb, B, nb) :: CL) FB m3 -> ps_outfile ps3 = ps_outfile s ->
      match i with Some _ => True | None => I = 0%Z end ->
      rw_cells usegs m3 (bv_unsigned sp + -128) hc -> cells_size hc = 40%nat -> FRS m3 ->
      rw_cells usegs m3 ERR [C4 ew] -> rw_cells usegs m3 MG (map (fun z => C1 (Z_to_bv 8 z)) magic) -> rw_cells usegs m3 EB [CB 256 e] ->
      rw_cells usegs m3 (P + 24) [C8 (Z_to_bv 64 B)] -> rw_cells usegs m3 (P + 672) [C8 (Z_to_bv 64 I)] ->
      (0 <= I < 2^64)%Z -> (1 <= nb)%Z ->
      fmt_at m3 SRC str -> (Z.of_nat (String.length str) + 1 = n)%Z -> (n <= 256)%Z ->
      map b8 msg = map (fun ch => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii ch))) (String.list_ascii_of_string str) ->
      Forall (fun z => 0 < z < 256)%Z msg ->
      implM usegs (ngc_fail MOps PR msg (ngc_p f qs sw BS0 MINOR qb nb bufdata sg i)) ps3 POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 ERR) (Z_to_bv 64 EB)
                 a0' (Z_to_bv 64 SRC) (Z_to_bv 64 n) a3' a4' a5' a6' a7'
                 x2 (Z_to_bv 64 P) x4 x5 (Z_to_bv 64 (P + 648)) x7 (Z_to_bv 64 1) x9 s10 s11 t3' t4' t5' t6')
            F (Z_to_bv 64 0x1700c) fc None m3 (seg_rom usegs)).
  Section Sz3.
  Variables ra' t0' t1' t2' a0' a3' a4' a5' a6' a7' t3' t4' t5' t6' x2 x4 x5 x7 x9 m3 ps3 SRC n str msg bufdata qb i sg B I nb e hc : ltac2:(SecDiet.SzSec.tyM 'ngc_mcp_fail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ngc_mcp_fail__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_mcp_fail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using CTX FREE HFL HPL P14 SFL. pin_using (fun (CTX FREE HFL HPL P14 SFL : unit) => tt).
 intros MI3 ST3 AG3 G3 OF3 HI HC3 Hhc FRS3 ERR3 MG3 HEB3 HPB HPI IR NB [SRCB SRCR] LN NB2 EMSG MOK.
    pose proof CTX as (G & LO & BU & SPM & TP & ALN & HinF & SITES & GL & GR & R1 & R2 & R3 & E1 & E2 & D1 & E4 & E8).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. pose proof (GIo_sp47 K _ _ _ _ _ G) as SP47. pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2^64)%Z in RSP.
    pose proof E2 as EBU. unfold rc_spmain in EBU.
    destruct P14 as [P1 P4].
    destruct (ngl_facts K HPL _ _ _ _ _ _ _ _ _ _ _ _ _ G3 NB) as ((B1 & B2 & B4) & APB & API & NPB).
    assert (CLB : forall a, in_block CL a -> (a < CEILZ)%Z).
    { intros a Ha. destruct (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _]. exact (proj2 Hc). }
    assert (LM : length msg = String.length str).
    { apply (f_equal (@length _)) in EMSG. rewrite !length_map, length_list_ascii in EMSG. exact EMSG. }
    pose proof (rw_cells_split_CB _ _ _ [] _ _ [] [Z.to_nat n; (256 - Z.to_nat n)%nat] HEB3 ltac:(cbn; lia)) as HE'. clear HEB3. cbn [mk_CB_cells app] in HE'.
    destruct (rw_cells_cut _ _ _ 1 HE') as [HE1 HE2]. clear HE'. cbn [firstn skipn cells_size csize Nat.add] in HE1, HE2.
    lazymatch type of HE2 with rw_cells _ _ ?A _ => replace A with (EB + n)%Z in HE2 by lia end.
    unfold ngc_fail. cbn [e_fenter e_fret fo_enter fo_ret fo_nop prims]. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_free prims free_opt ng_ifaces_ptr_of pc_buffer pc_self pc_priv ngc_p].
    unfold implM. iprefix.
    hide HC3. hide FRS3. hide ERR3. hide MG3. hide HE2. hide HPB. hide HPI.
    step. step.
    eapply evt_cut.
    { eapply (memcpy_specZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ EB SRC n);
        [reflexivity | reflexivity | reflexivity | exact SRCB | rewrite length_app, length_map, length_list_ascii; cbn [length]; lia | lia | exact HE1
        | lia | lia | lia | exact MI3]. }
    cbv beta. intros ms' PO. destruct PO as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & m4 & -> & MU4 & WM4 & MI4 & HE1' & _). clear HE1.
    replace (ret_pc (Z_to_bv 64 0x17014)) with (Z_to_bv 64 0x17014) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    assert (AGS : agrees_on (fun a => outside [(EB, EB + n)]%Z a) m3 m4) by (eapply agrees_on_of_munch; [exact MU4 | exact WM4 | intros a _ Ho; exact Ho]).
    assert (ST4 : stk usegs m4 lo (bv_unsigned sp + -128)).
    { eapply stk_transport_disjoint; [exact ST3 | exact MU4 | exact WM4 | cbn [disjoint_from]; unfold rc_lo in *; lia]. }
    assert (G4 : GIo K R ps3 (IBLK i I sg ++ (qs, P, 680%Z) :: (qb, B, nb) :: CL) FB m4).
    { eapply (GIo_client_frame K HFL SFL); [exact G3 | exact MU4 | exact WM4 |]. apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]. }
    unhide HC3. unhide FRS3. unhide ERR3. unhide MG3. unhide HE2. unhide HPB. unhide HPI.
    transport HC3 m4 AGS ltac:(intros a Ha; rewrite Hhc in Ha; cbn [outside]; lia).
    unfold ngc_FRS in FRS3. transport FRS3 m4 AGS ltac:(prs). transport ERR3 m4 AGS ltac:(prs).
    transport MG3 m4 AGS ltac:(intros a Ha; rewrite cells_size_map_C1, GL in Ha; cbn [outside]; lia).
    transport HE2 m4 AGS ltac:(prs). transport HPB m4 AGS ltac:(prs). transport HPI m4 AGS ltac:(prs).
    assert (AG4 : AGQ m4).
    { unfold ngc_AGQ in AG3 |- *. eapply agrees_on_trans; [exact AG3|]. eapply agrees_on_weaken; [exact AGS|].
      intros a [_ [Hn _]]; cbn [outside]. lia. }
    lazymatch type of HE2 with rw_cells _ _ _ [CB _ ?j] =>
      assert (HEB4 : rw_cells usegs m4 EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) j]) end.
    { join_cells HE1' HE2.
      eapply rw_cells_recell; [exact HE1' | pose proof (proj1 (proj1 HE1')) as WF; cbn in WF |- *; rewrite ?length_app, ?length_map, ?length_list_ascii in *; cbn [length] in *; repeat split; try lia; tauto |].
      cbn [cells_bytes cbytes app]. rewrite EMSG, <- app_assoc. reflexivity. }
    apply evt_done. eapply (ngc_fail3 HO K sites HFL SFL FREE ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m) with (i := i) (ni := (40 * ng_ifaces_size sg)%Z);
      [ exact CTX | exact MI4 | exact ST4 | exact AG4 | destruct i; exact G4 | exact HI | exact HC3 | exact Hhc | exact FRS3 | exact ERR3 | exact MG3 | exact HEB4
      | rewrite LM; lia | exact MOK | exact OF3 | exact HPB | exact HPI | exact IR | lia | lia ].
  Qed.
  End Sz3.
  Lemma ngc_mcp_fail : ltac:(let t := eval cbv delta [ngc_mcp_fail__stmt] in ngc_mcp_fail__stmt in exact t).
  Proof using CTX FREE HFL HPL P14 SFL. intros ra' t0' t1' t2' a0' a3' a4' a5' a6' a7' t3' t4' t5' t6' x2 x4 x5 x7 x9 m3 ps3 SRC n str msg bufdata qb i sg B I nb e hc. ltac2:(SecDiet.SzSec.closeP 'ngc_mcp_fail__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma hcells_cut : forall mX B,
    rw_cells usegs mX P (hcells B) ->
    rw_cells usegs mX (P + 24) [C8 (Z_to_bv 64 B)]
    /\ rw_cells usegs mX (P + 48) [C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF)); C4 (Z_to_bv 64 (Z.b2z sw))].
  Proof using Type. pin_using tt.
    intros mX B HC. unfold ngc_hcells, ngcells in HC.
    destruct (rw_cells_cut _ _ _ 4 HC) as [_ X]. destruct (rw_cells_cut _ _ _ 1 X) as [X1 X2]. destruct (rw_cells_cut _ _ _ 2 X2) as [_ X3]. destruct (rw_cells_cut _ _ _ 2 X3) as [X4 _].
    cbn [firstn skipn cells_size csize Nat.add app] in X1, X4. unfold PCAP_PRIV_OFF.
    split; [replace (P + 24)%Z with (P + Z.of_nat 24)%Z by lia; exact X1|].
    replace (P + 48)%Z with (P + Z.of_nat 24 + Z.of_nat 8 + Z.of_nat 16)%Z by lia. exact X4.
  Qed.
  Lemma ngcells_cut672 : forall mX sg I pad,
    rw_cells usegs mX (P + 648) (ng_cells sg I pad) -> rw_cells usegs mX (P + 672) [C8 (Z_to_bv 64 I)].
  Proof using Type. pin_using tt.
    intros mX sg I pad HN. unfold ng_cells in HN. destruct (rw_cells_cut _ _ _ 5 HN) as [_ X]. cbn [firstn skipn cells_size csize Nat.add app] in X.
    replace (P + 672)%Z with (P + 648 + Z.of_nat 24)%Z by lia. exact X.
  Qed.

  (* [comment removed for export] *)
  Hypothesis AI : add_interface_stmt HO K sites.

  Definition ngc_idb__stmt : Prop := forall (fuel : nat) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' x7 : word) (m4 : mem) (ps4 : PS)
           (qb : hptr) (B bufalloc : Z) (bufdata : list Z) (sg : pcap_ng_sf) (i : option hptr) (I : Z) (pad bs e cpad j0 j1 : list byte) (c : cursor),
      mem_inv usegs m4 -> stk usegs m4 lo (bv_unsigned sp + -128) -> AGQ m4 ->
      GIo K R ps4 (IBLK i I sg ++ (qs, P, 680%Z) :: (qb, B, bufalloc) :: CL) FB m4 -> ps_outfile ps4 = ps_outfile s ->
      rw_cells usegs m4 (bv_unsigned sp + -128) [CB 8 j0] -> rw_cells usegs m4 (bv_unsigned sp + -120) (cursor_cells B c cpad) ->
      rw_cells usegs m4 (bv_unsigned sp + -96) [CB 8 j1] -> FRS m4 ->
      rw_cells usegs m4 ERR [C4 ew] -> rw_cells usegs m4 MG (map (fun z => C1 (Z_to_bv 8 z)) magic) -> rw_cells usegs m4 EB [CB 256 e] ->
      rw_cells usegs m4 P (hcells B) -> rw_cells usegs m4 (P + 648) (ng_cells sg I pad) ->
      ng_user_tsresol sg = 1000000%Z -> ng_max_blocksize sg = INITIAL_MAX_BLOCKSIZE -> (0 <= ng_ifcount sg < 2^32)%Z -> (0 <= ng_ifaces_size sg < 2^32)%Z ->
      ifaces_ok (pL qb bufalloc bufdata sg i) I m4 ->
      rw_cells usegs m4 B [CB (Z.to_nat bufalloc) bs] -> firstn (length bufdata) bs = map b8 bufdata ->
      Z.of_nat (length bufdata) = (cur_remaining c + 12)%Z ->
      cur_off c = 8%Z -> (0 <= cur_remaining c)%Z -> (cur_remaining c + 12 <= bufalloc)%Z -> (cur_remaining c + 12 <= 2^30)%Z -> cur_block_type c = 1%Z ->
      (0 <= bufalloc < 2^32)%Z -> (BS0 <= bufalloc)%Z -> Forall (fun z => 0 <= z < 256)%Z bufdata ->
      implM usegs (mbind (ngc_K MOps PR fuel (RB_Ok c (pL qb bufalloc bufdata sg i))) (ngc_loop_tail MOps PR 0)) ps4 POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 ERR) (Z_to_bv 64 EB) a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 FA) (Z_to_bv 64 P) (Z_to_bv 64 1) (Z_to_bv 64 2) (Z_to_bv 64 (P + 648)) x7 (Z_to_bv 64 1) (Z_to_bv 64 6) s10 s11 t3' t4' t5' t6')
            F (Z_to_bv 64 0x16e94) fc None m4 (seg_rom usegs)).
  Section Sz6.
  Variables fuel ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' x7 m4 ps4 qb B bufalloc bufdata sg i I pad bs e cpad j0 j1 c : ltac2:(SecDiet.SzSec.tyM 'ngc_idb__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @fuel).
  Lemma ngc_idb__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_idb__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AI BS0R CTX FREE HFL HPL MINR P14 P16 SFL SNPRINTF. pin_using (fun (AI BS0R CTX FREE HFL HPL MINR P14 P16 SFL SNPRINTF : unit) => tt).
 intros MI4 ST4 AG4 G4 OF4 HD4 HCUR4 HTL4 FRS4 ERR4 MG4 HEB4 CELLS NG4 UTS MB IC IS HIF BUF4 PFX LENB COFF CREM CR1 CR2 CBT BAR BSB GRD.
    pose proof CTX as (G & LO & BU & SPM & TP & ALN & HinF & SITES & GL & GR & R1 & R2 & R3 & E1 & E2 & D1 & E4 & E8).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. pose proof (GIo_sp47 K _ _ _ _ _ G) as SP47. pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2^64)%Z in RSP.
    pose proof E2 as EBU. unfold rc_spmain in EBU.
    destruct P14 as [P1 P4].
    destruct (ngl_facts K HPL _ _ _ _ _ _ _ _ _ _ _ _ _ G4 ltac:(lia)) as ((B1 & B2 & B4) & APB & API & NPB).
    assert (CLB : forall a, in_block CL a -> (a < CEILZ)%Z).
    { intros a Ha. destruct (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _]. exact (proj2 Hc). }
    assert (HI : match i with Some _ => True | None => I = 0%Z end).
    { unfold ifaces_ok in HIF. cbn [pc_priv ngc_p] in HIF. destruct i; [exact Logic.I| exact (proj1 HIF)]. }
    (* [comment removed for export] *)
    unfold ngc_K. rewrite CBT. unfold BT_IDB. cbn [Z.eqb Pos.eqb]. cbv iota.
    unfold get_from_block_data. rewrite COFF, CBT.
    unfold cursor_cells in HCUR4. rewrite COFF, CBT in HCUR4.
    assert (IR : (0 <= I < 2^64)%Z) by (destruct i as [q|]; [destruct (API sg q eq_refl) as (I1 & I4 & _); lia| cbn in HI; lia]).
    (* [comment removed for export] *)
    assert (HC40 : forall mX ccs, rw_cells usegs mX (bv_unsigned sp + -128) [CB 8 j0] -> rw_cells usegs mX (bv_unsigned sp + -120) ccs -> cells_size ccs = 24%nat ->
                   rw_cells usegs mX (bv_unsigned sp + -96) [CB 8 j1] ->
                   rw_cells usegs mX (bv_unsigned sp + -128) ([CB 8 j0] ++ ccs ++ [CB 8 j1]) /\ cells_size ([CB 8 j0] ++ ccs ++ [CB 8 j1]) = 40%nat).
    { intros mX ccs X1 X2 X3 X4. split; [| rewrite !cells_size_app, X3; reflexivity].
      pose proof (rw_cells_uncut _ _ _ _ _ X1 X2 ltac:(cbn; lia)) as J1.
      exact (rw_cells_uncut _ _ _ _ _ J1 X4 ltac:(rewrite cells_size_app, X3; cbn; lia)). }
    hide HD4. hide HTL4. hide FRS4. hide ERR4. hide MG4. hide HEB4. hide CELLS. hide NG4. hide BUF4.
    unfold implM. iprefix.
    (* [comment removed for export] *)
    do 4 step.
    (* [comment removed for export] *)
    step. rewrite (and7_aligned (bv_unsigned sp + -120)) by (fastfirst (first [ noevar_assumption |lia | apply aligned16_8; [exact ALN| reflexivity]])). step.
    if_false.
    step. step.
    unfold bv_ltu. rewrite (unsigned_lit 8), (unsigned_lit (cur_remaining c)) by lia.
    destruct (Z.lt_ge_cases (cur_remaining c) 8) as [RLT|RGE].
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.ltb_lt _ _) RLT). cbn [negb]. cbv iota.
      apply evt_done. apply (implM_retb usegs). unfold ngc_loop_tail.
      unfold ngc_fail. cbn [e_fenter e_fret fo_enter fo_ret fo_nop prims]. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_free prims free_opt ng_ifaces_ptr_of pc_buffer pc_self pc_priv ngc_p].
      unfold implM. iprefix.
      carve_frame 16%nat ST4.
      pose proof (munch_refl [(bv_unsigned sp + -144, bv_unsigned sp + -128)]%Z m4) as MUg. pose proof (wmono_refl usegs m4) as WMg.
      step. pstep. step. rewrite ?(sx32_small 1) by lia. do 6 step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m4a end.
      assert (MSG : fmt_at m4a 0x10cd0 "block of type %u in pcapng dump file is too short"%string)
        by (apply (fmt_at_intro m4a _ _ MI4); [vm_compute; reflexivity| lia| cbn; lia]).
      assert (G4a : GIo K R ps4 (IBLK i I sg ++ (qs, P, 680%Z) :: (qb, B, bufalloc) :: CL) FB m4a).
      { eapply (GIo_client_frame K HFL SFL); [exact G4 | exact MUg | exact WMg |]. apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]. }
      assert (AGSg : agrees_on (fun a => outside [(bv_unsigned sp + -144, bv_unsigned sp + -128)]%Z a) m4 m4a)
        by (eapply agrees_on_of_munch; [exact MUg | exact WMg | intros a _ Ho; exact Ho]).
      unhide HEB4. transport HEB4 m4a AGSg ltac:(prs).
      name_sp sp (-144)%Z.
      eapply evt_cut.
      { eapply (SNPRINTF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R ps4 (IBLK i I sg ++ (qs, P, 680%Z) :: (qb, B, bufalloc) :: CL) FB lo EB 256%Z 0x10cd0%Z
                  "block of type %u in pcapng dump file is too short"%string [AInt 1] e);
          [ split; [exact G4a|]; split; [rewrite Hsp; exact ST4|]; split; [unfold rc_lo; lia|]; split; [unfold STDIO_STACK; rewrite Hsp; lia|];
            split; [rewrite Hsp; lia|]; split; [exact MI4|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]
          | reflexivity | reflexivity | reflexivity | lia | exact MSG | vm_compute; reflexivity | cbn; lia
          | cbn [length firstn]; constructor; [reflexivity| constructor] | exact HEB4 | right; rewrite Hsp; lia ]. }
      cbv beta. intros ms' PO. destruct PO as (av5 & m5 & junk5 & E & MU5 & WM5 & MI5 & ST5 & -> & HEB5).
      unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 0x174e0)) with (Z_to_bv 64 0x174e0) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      assert (AGS5 : agrees_on (fun a => outside [(bv_unsigned sp + -144 - STDIO_STACK, bv_unsigned sp + -144); (EB, EB + 256)]%Z a) m4a m5)
        by (eapply agrees_on_of_munch; [exact MU5 | exact WM5 | intros a _ Ho; exact Ho]).
      unfold STDIO_STACK in AGS5, MU5.
      transport FR m5 AGS5 ltac:(prs).
      hide HEB5. hide HCUR4.
      step. step. step. step.
      replace (ret_pc (Z_to_bv 64 0x16ea4)) with (Z_to_bv 64 0x16ea4) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      step. rewrite (eqb_lits_eq 0 0 eq_refl). cbv iota.
      release_frame FR ST5 (bv_unsigned sp + -128)%Z.
      assert (AG45 : agrees_on (fun a => outside [(bv_unsigned sp + -144 - 65536, bv_unsigned sp + -128); (EB, EB + 256)]%Z a) m4 m5).
      { eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AGSg|] | eapply agrees_on_weaken; [exact AGS5|]]; intros a Ha; cbn [outside] in Ha |- *; lia. }
      assert (G5 : GIo K R ps4 (IBLK i I sg ++ (qs, P, 680%Z) :: (qb, B, bufalloc) :: CL) FB m5).
      { eapply (GIo_client_frame K HFL SFL); [exact G4a | exact MU5 | exact WM5 |].
        apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia|]. apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]. }
      assert (AG5 : AGQ m5).
      { unfold ngc_AGQ in AG4 |- *. eapply agrees_on_trans; [exact AG4|]. eapply agrees_on_weaken; [exact AG45|].
        intros a [[Ha|Ha] [Hn _]]; cbn [outside]; [lia|]. pose proof (CLB a Ha). lia. }
      unhide HD4. unhide HCUR4. unhide HTL4. unhide FRS4. unhide ERR4. unhide MG4. unhide HEB5. unhide CELLS. unhide NG4.
      transport HD4 m5 AG45 ltac:(prs). transport HCUR4 m5 AGS5 ltac:(prs). transport HTL4 m5 AG45 ltac:(prs).
      unfold ngc_FRS in FRS4. transport FRS4 m5 AG45 ltac:(prs). transport ERR4 m5 AG45 ltac:(prs). transport MG4 m5 AG45 ltac:(prsMG GL).
      transport CELLS m5 AG45 ltac:(unfold ngc_hcells, ngcells; prs). transport NG4 m5 AG45 ltac:(unfold ng_cells; prs).
      destruct (HC40 m5 _ HD4 HCUR4 ltac:(reflexivity) HTL4) as [HC Hhc].
      assert (EMSG : Fmt.snprintf 256 "block of type %u in pcapng dump file is too short"%string [AInt 1] = Msg.block_too_short 1)
        by (unfold Msg.block_too_short, PCAP_ERRBUF_SIZE; reflexivity).
      pose proof (snprintf_length 256 "block of type %u in pcapng dump file is too short"%string [AInt 1]) as LS. change (Z.to_nat (256 - 1)) with 255%nat in LS.
      rewrite EMSG in LS, HEB5. change (Z.to_nat 256) with 256%nat in HEB5.
      replace (256 - length (Msg.block_too_short 1) - 1)%nat with (255 - length (Msg.block_too_short 1))%nat in HEB5 by lia.
      apply evt_done.
      eapply (ngc_fail3 HO K sites HFL SFL FREE ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m) with (i := i) (ni := (40 * ng_ifaces_size sg)%Z);
        [ exact CTX | exact MI5 | exact ST5 | exact AG5 | destruct i; exact G5 | exact HI | exact HC | exact Hhc | exact FRS4 | exact ERR4 | exact MG4 | exact HEB5
        | clear - LS; lia | unfold Msg.block_too_short; apply snprintf_ok; [vm_compute; reflexivity| apply args_ok_ints1] | exact OF4
        | exact (proj1 (hcells_cut _ _ CELLS)) | exact (ngcells_cut672 _ _ _ _ NG4) | exact IR | lia | lia ].
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.ltb_ge _ _) RGE). cbn [negb]. cbv iota.
      cbn [pc_swapped ngc_p pc_bufdata].
      assert (SNEZ : forall x, (0 < x < 2^64)%Z -> v_sltu z64 (Z_to_bv 64 x) = Z_to_bv 64 1).
      { intros x Hx. rewrite v_sltu_b2z. change (bv_unsigned z64) with 0%Z. rewrite (unsigned_lit x) by lia. destruct (Z.ltb_spec 0 x); [reflexivity| exfalso; lia]. }
      assert (SEQZ : forall x, (0 < x < 2^64)%Z -> v_sltiu (Z_to_bv 64 x) 1 = Z_to_bv 64 0).
      { intros x Hx. unfold v_sltiu. rewrite (unsigned_lit x) by lia. change (bv_wrap 64 1) with 1%Z. destruct (Z.ltb_spec x 1); [exfalso; lia| reflexivity]. }
      pose proof (munch_refl [(bv_unsigned sp + -120, bv_unsigned sp + -96)]%Z m4) as MUc. pose proof (wmono_refl usegs m4) as WMc.
      step. step.
      replace (8 + (B + 8))%Z with (B + 16)%Z by lia.
      step. if_cases Kc; [zify_cond Kc; exfalso; lia|]. clear Kc.
      step. rewrite (SNEZ (B + 8)%Z) by lia. step. rewrite (SEQZ (B + 16)%Z) by lia. step.
      replace (Z.lxor (bv_unsigned (Z_to_bv 64 1)) (bv_unsigned z64)) with 1%Z by reflexivity.
      step. if_false.
      step. step. step. step. step.
      replace (ret_pc (Z_to_bv 64 0x16ea4)) with (Z_to_bv 64 0x16ea4) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      rewrite ?(unsigned_lit (cur_remaining c)) in HCUR4 |- * by lia.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m5 end.
      assert (AGS45 : agrees_on (fun a => outside [(bv_unsigned sp + -120, bv_unsigned sp + -96)]%Z a) m4 m5)
        by (eapply agrees_on_of_munch; [exact MUc | exact WMc | intros a _ Ho; exact Ho]).
      assert (G5 : GIo K R ps4 (IBLK i I sg ++ (qs, P, 680%Z) :: (qb, B, bufalloc) :: CL) FB m5).
      { eapply (GIo_client_frame K HFL SFL); [exact G4 | exact MUc | exact WMc |]. apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]. }
      assert (AG5 : AGQ m5).
      { unfold ngc_AGQ in AG4 |- *. eapply agrees_on_trans; [exact AG4|]. eapply agrees_on_weaken; [exact AGS45|].
        intros a [[Ha|Ha] _]; cbn [outside]; [lia|]. pose proof (CLB a Ha). lia. }
      assert (HIF5 : ifaces_ok (pL qb bufalloc bufdata sg i) I m5).
      { eapply ifaces_ok_agree; [exact AGS45 | | exact HIF]. intros sg' q E a Ha. cbn [pc_priv ngc_p] in E. destruct (API sg' q E) as (I1 & I4 & _). cbn [outside]. lia. }
      unhide HD4. unhide HTL4. unhide FRS4. unhide ERR4. unhide MG4. unhide HEB4. unhide CELLS. unhide NG4. unhide BUF4.
      transport HD4 m5 AGS45 ltac:(prs). transport HTL4 m5 AGS45 ltac:(prs). unfold ngc_FRS in FRS4. transport FRS4 m5 AGS45 ltac:(prs).
      transport ERR4 m5 AGS45 ltac:(prs). transport MG4 m5 AGS45 ltac:(prsMG GL). transport HEB4 m5 AGS45 ltac:(prs).
      transport CELLS m5 AGS45 ltac:(unfold ngc_hcells, ngcells; prs). transport NG4 m5 AGS45 ltac:(unfold ng_cells; prs). transport BUF4 m5 AGS45 ltac:(prs).
      clear MUc WMc AG4 G4 HIF.
      (* [comment removed for export] *)
      step. rewrite (eqb_lits_false (B + 8) 0) by lia. cbv iota.
      step. step. unfold ngc_hcells, ngcells in CELLS. step. rewrite (sx32_small (Z.b2z sw)) by (destruct sw; cbn; lia).
      step. rewrite (and3_aligned (B + 8)) by (fastfirst (first [ noevar_assumption |lia | replace (B + 8)%Z with (B + 0 + 8)%Z by lia; apply aligned16_4; [apply aln16_add; [exact B2| reflexivity] | reflexivity]])).
      step.
      replace (cur_remaining c + -8)%Z with (cur_remaining c - 8)%Z in HCUR4 by lia.
      (* [comment removed for export] *)
      assert (CALL : forall (rax a1x a2x a3x a4x a5x a6x : word) (m6 : mem) (bd : list Z) (bs5 : list byte),
        bd = (if sw then swap_field 4 12 (swap_field 2 8 bufdata) else bufdata) ->
        mem_inv usegs m6 -> stk usegs m6 lo (bv_unsigned sp + -128) -> AGQ m6 ->
        GIo K R ps4 (IBLK i I sg ++ (qs, P, 680%Z) :: (qb, B, bufalloc) :: CL) FB m6 ->
        rw_cells usegs m6 (bv_unsigned sp + -128) [CB 8 j0] ->
        rw_cells usegs m6 (bv_unsigned sp + -120) (cursor_cells B (mkCursor 16 (cur_remaining c - 8) 1) cpad) ->
        rw_cells usegs m6 (bv_unsigned sp + -96) [CB 8 j1] -> FRS m6 ->
        rw_cells usegs m6 ERR [C4 ew] -> rw_cells usegs m6 MG (map (fun z => C1 (Z_to_bv 8 z)) magic) -> rw_cells usegs m6 EB [CB 256 e] ->
        rw_cells usegs m6 P (hcells B) -> rw_cells usegs m6 (P + 648) (ng_cells sg I pad) ->
        ifaces_ok (pL qb bufalloc bd sg i) I m6 ->
        rw_cells usegs m6 B [CB (Z.to_nat bufalloc) bs5] -> firstn (length bd) bs5 = map b8 bd -> length bd = length bufdata ->
        Forall (fun z => 0 <= z < 256)%Z bd ->
        evt usegs (fun ms1 => impl usegs (at_node usegs) (npeek usegs)
             ((Monad.mbind (mo_bind MOps (add_interface MOps PR (pL qb bufalloc bd sg i) 8 (mkCursor 16 (cur_remaining c - 8) 1))
                             (fun x : bool * cursor * pcapT * list Z => let '(ok, _, p, m) := x in
                                if ok then mo_ret MOps (@inr (list Z) Z 8%Z, p) else mo_ret MOps (@inl (list Z) Z m, p)))
                          (ngc_loop_tail MOps PR 0)) ps4)
             (epost (fun p0 => POSTQ (fst p0) (snd p0))) ms1)
          (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 ERR) (Z_to_bv 64 EB) (Z_to_bv 64 P) a1x a2x a3x a4x a5x a6x a7'
                   (Z_to_bv 64 (B + 8)) (Z_to_bv 64 P) (Z_to_bv 64 0) (Z_to_bv 64 2) (Z_to_bv 64 (P + 648)) x7 (Z_to_bv 64 1) (Z_to_bv 64 6) s10 s11 t3' t4' t5' t6')
              F (Z_to_bv 64 0x16f08) fc None m6 (seg_rom usegs))).
      { intros until bs5. intros Ebd MI6 ST6 AG6 G6 HD5 HCUR5 HTL5 FRS5 ERR5 MG5 HEB5 CELLS5 NG5 HIF6 BUF5 PFX5 LEN5 GRD5.
        clear HCUR4 HIF5 PFX GRD.
        assert (LBD : Z.of_nat (length bd) = (cur_remaining c + 12)%Z) by (rewrite LEN5; exact LENB).
        hide HD5. hide HTL5. hide FRS5. hide ERR5. hide MG5. hide HEB5. hide CELLS5. hide NG5. hide BUF5. hide HCUR5.
        do 4 step.
        unhide HEB5. unhide CELLS5. unhide NG5. unhide BUF5. unhide HCUR5.
        apply evt_done. apply (implM_bind_assoc usegs). name_sp sp (-128)%Z. eapply (implM_bind usegs).
        { eapply (AI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 R ps4 [] ((qs, P, 680%Z) :: (qb, B, bufalloc) :: CL) FB P B I (bv_unsigned sp + -120)%Z EB lo 8%Z
                     (pL qb bufalloc bd sg i) sg i (mkCursor 16 (cur_remaining c - 8) 1) bs5 e pad cpad);
            [ split; [cbn [app]; exact G6|]; split; [rewrite Hsp; exact ST6|]; split; [unfold rc_lo; lia|]; split; [unfold ADD_INTERFACE_STACK, MALLOC_STACK; rewrite Hsp; lia|];
              split; [rewrite Hsp; lia|]; split; [exact MI6|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]
            | reflexivity | left; reflexivity | right; left; reflexivity | unfold PCAP_NG_SF_TOTAL; cbn [pc_bufalloc ngc_p]; lia
            | reflexivity | reflexivity | reflexivity | reflexivity
            | exact (proj2 (hcells_cut _ _ CELLS5)) | exact NG5 | exact HIF6 | rewrite UTS; lia | rewrite MB; unfold INITIAL_MAX_BLOCKSIZE; lia
            | exact BUF5 | exact PFX5 | cbn [pc_bufdata pc_bufalloc ngc_p]; lia | exact GRD5
            | exact HCUR5 | rewrite ?Hsp; lia | lia | rewrite ?Hsp; apply aligned16_8; [exact ALN| reflexivity]
            | lia | reflexivity | reflexivity | cbn [cur_remaining]; lia | cbn [cur_off cur_remaining pc_bufdata ngc_p]; lia | cbn [cur_block_type]; lia
            | exact HEB5 | left; rewrite Hsp; lia ]. }
        intros [[[ok c5] p5] msg5] ps5 ms5 PO.
        destruct PO as (a0v & m7 & s' & i' & I' & pad' & bs' & E & OF5 & MI7 & ST7 & AG7 & EP & G7 & NG7 & U1 & U2 & U3 & U4 & BUF7 & PFX7 & LEN7 & GR7 & -> & RM).
        unfold hpost_regs in E. destruct_exs E. subst ms5. rewrite Hsp in *. unname_sp.
        replace (ret_pc (Z_to_bv 64 0x16f18)) with (Z_to_bv 64 0x16f18) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        cbn [app] in G7. set (bd' := pc_bufdata p5) in *. rewrite EP. cbn [pc_bufdata pc_bufalloc ngc_p] in LEN7.
        assert (OF7 : ps_outfile ps5 = ps_outfile s) by (rewrite OF5; exact OF4).
        destruct (ngl_facts K HPL _ _ _ _ _ _ _ _ _ _ _ _ _ G7 ltac:(lia)) as (_ & _ & API' & _).
        unhide HD5. unhide HTL5. unhide FRS5. unhide ERR5. unhide MG5.
        cbn [pc_bufalloc ngc_p] in AG7. unfold PCAP_PRIV_OFF, PCAP_NG_SF_TOTAL in AG7.
        transport HD5 m7 AG7 ltac:(unfold PCAP_PRIV_OFF, PCAP_NG_SF_TOTAL; prs). transport HTL5 m7 AG7 ltac:(unfold PCAP_PRIV_OFF, PCAP_NG_SF_TOTAL; prs).
        unfold ngc_FRS in FRS5. transport FRS5 m7 AG7 ltac:(unfold PCAP_PRIV_OFF, PCAP_NG_SF_TOTAL; prs). transport ERR5 m7 AG7 ltac:(unfold PCAP_PRIV_OFF, PCAP_NG_SF_TOTAL; prs).
        transport MG5 m7 AG7 ltac:(prsMG GL).
        assert (INP5 : forall a, (P <= a < P + 680)%Z -> in_block ([] ++ (qs, P, 680%Z) :: (qb, B, bufalloc) :: CL) a).
        { intros a Ha. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
        transport CELLS5 m7 AG7 ltac:(unfold ngc_hcells, ngcells, PCAP_PRIV_OFF, PCAP_NG_SF_TOTAL; prs).
        assert (AG07 : AGQ m7).
        { unfold ngc_AGQ in AG6 |- *. eapply agrees_on_trans; [exact AG6|]. eapply agrees_on_weaken; [exact AG7|].
          intros a [[Ha|Ha] [Hn _]]; unfold PCAP_PRIV_OFF, PCAP_NG_SF_TOTAL; cbn [app]; [split; [left; lia| lia]|].
          pose proof (CLB a Ha). pose proof (NPB a Ha). split; [right; unfold in_block in Ha |- *; do 2 apply Exists_cons_tl; exact Ha| lia]. }
        unfold implM. iprefix.
        destruct ok; cbn [Z.b2z].
        - (* [comment removed for export] *)
          destruct RM as (HIF7 & (cpad' & HCUR7) & CR1' & CR2' & CR3' & CBT' & HEB7 & ->). rewrite EP in HIF7.
          hide HD5. hide HTL5. hide FRS5. hide ERR5. hide MG5. hide CELLS5. hide NG7. hide BUF7. hide HCUR7. hide HEB7.
          step. rewrite (eqb_lits_false 1 0) by lia. cbv iota.
          step. rewrite (eqb_lits_eq 0 0 eq_refl). cbv iota.
          unhide HD5. unhide HTL5. unhide FRS5. unhide ERR5. unhide MG5. unhide CELLS5. unhide NG7. unhide BUF7. unhide HCUR7. unhide HEB7.
          destruct (HC40 m7 _ HD5 HCUR7 ltac:(reflexivity) HTL5) as [HC Hhc].
          apply evt_done. apply (implM_retb usegs). unfold ngc_loop_tail.
          eapply (ngc_ok_tail HO K sites HFL SFL HPL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m R s CL FB lo MG FA EB ERR f magic CTX
                    qs P sw BS0 MINOR ew (conj P1 P4) P16 BS0R MINR);
            [ exact MI7 | exact ST7 | exact AG07 | exact G7 | exact OF7 | exact HC | exact Hhc | exact FRS5 | exact ERR5 | exact MG5 | exact HEB7
            | exact CELLS5 | exact NG7 | rewrite U1; exact UTS | rewrite U2; exact MB | exact U3 | exact U4 | exact HIF7 | exact BUF7 | exact PFX7
            | cbn [pc_bufdata pc_bufalloc ngc_p set_ng set_priv set_bufdata]; lia | cbn [pc_bufalloc ngc_p set_ng set_priv set_bufdata]; lia | cbn [pc_bufalloc ngc_p set_ng set_priv set_bufdata]; lia | exact GR7 ].
        - (* [comment removed for export] *)
          destruct RM as (CLOS & (ccs' & HCUR7 & Hccs') & (junk7 & HEB7) & LENM & MOK).
          hide HD5. hide HTL5. hide FRS5. hide ERR5. hide MG5. hide CELLS5. hide NG7. hide BUF7. hide HCUR7. hide HEB7.
          step. rewrite (eqb_lits_eq 0 0 eq_refl). cbv iota.
          unhide HD5. unhide HTL5. unhide FRS5. unhide ERR5. unhide MG5. unhide CELLS5. unhide NG7. unhide BUF7. unhide HCUR7. unhide HEB7.
          destruct (HC40 m7 _ HD5 HCUR7 Hccs' HTL5) as [HC Hhc].
          apply evt_done. apply (implM_retb usegs). unfold ngc_loop_tail. unfold ngc_fail. cbn [e_fenter e_fret fo_enter fo_ret fo_nop prims]. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_free prims free_opt ng_ifaces_ptr_of pc_buffer pc_self pc_priv ngc_p].
          assert (HI' : match i' with Some _ => True | None => I' = 0%Z end) by (unfold ng_ifaces_closable in CLOS; destruct i'; [exact Logic.I| exact CLOS]).
          assert (IR' : (0 <= I' < 2^64)%Z) by (destruct i' as [q|]; [destruct (API' s' q eq_refl) as (I1 & I4 & _); lia| cbn in HI'; lia]).
          eapply (ngc_fail3 HO K sites HFL SFL FREE ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m) with (i := i') (ni := (40 * ng_ifaces_size s')%Z);
            [ exact CTX | exact MI7 | exact ST7 | exact AG07 | destruct i'; exact G7 | exact HI' | exact HC | exact Hhc | exact FRS5 | exact ERR5 | exact MG5 | exact HEB7
            | exact LENM | exact MOK | exact OF7 | exact (proj1 (hcells_cut _ _ CELLS5)) | exact (ngcells_cut672 _ _ _ _ NG7) | exact IR' | lia | lia ]. }
      destruct sw; cbn [Z.b2z].
      + (* [comment removed for export] *)
        rewrite (eqb_lits_false 1 0) by lia. cbv iota.
        step. if_false.
        destruct (split_at8 bufdata 8 ltac:(lia)) as (pre8 & l0 & l1 & r0 & r1 & n0 & n1 & n2 & n3 & post & Ebuf & Lpre8).
        assert (GX : (0 <= l0 < 256 /\ 0 <= l1 < 256 /\ 0 <= r0 < 256 /\ 0 <= r1 < 256 /\ 0 <= n0 < 256 /\ 0 <= n1 < 256 /\ 0 <= n2 < 256 /\ 0 <= n3 < 256)%Z).
        { rewrite Ebuf in GRD. apply Forall_app in GRD as [_ GB].
          pose proof (Forall_inv GB) as X0. apply Forall_inv_tail in GB. pose proof (Forall_inv GB) as X1. apply Forall_inv_tail in GB.
          pose proof (Forall_inv GB) as X2. apply Forall_inv_tail in GB. pose proof (Forall_inv GB) as X3. apply Forall_inv_tail in GB.
          pose proof (Forall_inv GB) as X4. apply Forall_inv_tail in GB. pose proof (Forall_inv GB) as X5. apply Forall_inv_tail in GB.
          pose proof (Forall_inv GB) as X6. apply Forall_inv_tail in GB. pose proof (Forall_inv GB) as X7.
          cbv beta in X0, X1, X2, X3, X4, X5, X6, X7. lia. }
        destruct GX as (L0 & L1 & R0' & R1' & N0 & N1 & N2 & N3).
        pose proof PFX as PFX0. rewrite Ebuf in PFX0.
        change (pre8 ++ l0 :: l1 :: r0 :: r1 :: n0 :: n1 :: n2 :: n3 :: post) with (pre8 ++ [l0; l1; r0; r1; n0; n1; n2; n3] ++ post) in PFX0.
        destruct (pfx_decomp pre8 [l0; l1; r0; r1; n0; n1; n2; n3] post bs PFX0) as (bsr & Ebs & PFXr). cbn [map] in Ebs.
        pose proof BUF4 as BX. rewrite Ebs in BX.
        assert (Lbsr : (length pre8 + 8 + length bsr = Z.to_nat bufalloc)%nat).
        { pose proof (proj1 (proj1 BX)) as WF. cbn in WF. rewrite !length_app, length_map in WF. cbn in WF. lia. }
        pose proof (rw_cells_recell _ _ _ [CB (length pre8) (map b8 pre8); C2 (Z_to_bv 64 (l0 + 256 * l1)); C2 (Z_to_bv 64 (r0 + 256 * r1)); C4 (Z_to_bv 64 (le4val n0 n1 n2 n3)); CB (length bsr) bsr] BX
                      ltac:(cbn; rewrite length_map; repeat split; fastfirst (first [reflexivity | lia]))
                      ltac:(cbn [cells_bytes cbytes app]; rewrite !le2_lit, le4_lit by lia; rewrite !app_nil_r; cbn [app]; reflexivity)) as BX'.
        destruct (rw_cells_cut _ _ _ 1 BX') as [HB0 BX2]. destruct (rw_cells_cut _ _ _ 3 BX2) as [HX HBR]. clear BX BX' BX2 BUF4.
        cbn [firstn skipn cells_size csize Nat.add app] in HB0, HX, HBR. rewrite Lpre8 in HX, HBR.
        replace (B + Z.of_nat 8)%Z with (B + 8)%Z in HX by lia. replace (B + Z.of_nat 8 + Z.of_nat 8)%Z with (B + 16)%Z in HBR by lia.
        hide HD4. hide HCUR4. hide HTL4. hide FRS4. hide ERR4. hide MG4. hide HEB4. hide CELLS. hide NG4. hide HB0. hide HBR.
        eapply evt_cut.
        { eapply (idb_swap_block _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 (B + 8)%Z l0 l1 r0 r1 n0 n1 n2 n3);
            [assumption | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia | reflexivity | exact HX]. }
        cbv beta. intros ms' PO. destruct PO as (z1 & z2 & z3 & z4 & z5 & m6 & -> & MU6 & WM6 & MI6 & HX6). clear HX.
        assert (AGS56 : agrees_on (fun a => outside [(B + 8, B + 8 + 8)]%Z a) m5 m6) by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
        assert (ST6 : stk usegs m6 lo (bv_unsigned sp + -128)).
        { eapply stk_transport_disjoint; [eassumption | exact MU6 | exact WM6 | cbn [disjoint_from]; unfold rc_lo in *; lia]. }
        assert (G6 : GIo K R ps4 (IBLK i I sg ++ (qs, P, 680%Z) :: (qb, B, bufalloc) :: CL) FB m6).
        { eapply (GIo_client_frame K HFL SFL); [exact G5 | exact MU6 | exact WM6 |]. apply Forall_cons; [| apply Forall_nil]. right. apply ngl_iv_B; lia. }
        assert (AG6 : AGQ m6).
        { unfold ngc_AGQ in AG5 |- *. eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AGS56|].
          intros a [[Ha|Ha] _]; cbn [outside]; [lia|]. pose proof (NPB a Ha). lia. }
        assert (HIF6 : ifaces_ok (pL qb bufalloc (pre8 ++ l1 :: l0 :: r0 :: r1 :: n3 :: n2 :: n1 :: n0 :: post) sg i) I m6).
        { assert (HIF' : ifaces_ok (pL qb bufalloc (pre8 ++ l1 :: l0 :: r0 :: r1 :: n3 :: n2 :: n1 :: n0 :: post) sg i) I m5) by exact HIF5.
          eapply ifaces_ok_agree; [exact AGS56 | | exact HIF']. intros sg' q E a Ha. cbn [pc_priv ngc_p] in E. destruct (API sg' q E) as (I1 & I4 & IP & IB). cbn [outside]. lia. }
        unhide HD4. unhide HCUR4. unhide HTL4. unhide FRS4. unhide ERR4. unhide MG4. unhide HEB4. unhide CELLS. unhide NG4. unhide HB0. unhide HBR.
        transport HD4 m6 AGS56 ltac:(prs). transport HCUR4 m6 AGS56 ltac:(unfold cursor_cells; prs). transport HTL4 m6 AGS56 ltac:(prs). transport FRS4 m6 AGS56 ltac:(prs).
        transport ERR4 m6 AGS56 ltac:(prs). transport MG4 m6 AGS56 ltac:(prsMG GL). transport HEB4 m6 AGS56 ltac:(prs).
        transport CELLS m6 AGS56 ltac:(prs). transport NG4 m6 AGS56 ltac:(unfold ng_cells; prs).
        transport HB0 m6 AGS56 ltac:(prs). transport HBR m6 AGS56 ltac:(prs).
        assert (BUF6 : rw_cells usegs m6 B [CB (Z.to_nat bufalloc) (map b8 pre8 ++ [b8 l1; b8 l0; b8 r0; b8 r1; b8 n3; b8 n2; b8 n1; b8 n0] ++ bsr)]).
        { replace (B + 8)%Z with (B + Z.of_nat (cells_size [CB (length pre8) (map b8 pre8)]))%Z in HX6 by (cbn; lia).
          pose proof (rw_cells_uncut _ _ _ _ _ HB0 HX6 ltac:(cbn; lia)) as J1.
          replace (B + 16)%Z with (B + Z.of_nat (cells_size ([CB (length pre8) (map b8 pre8)] ++ [C2 (Z_to_bv 64 (l1 + 256 * l0)); C2 (Z_to_bv 64 (r0 + 256 * r1)); C4 (Z_to_bv 64 (le4val n3 n2 n1 n0))])))%Z in HBR by (cbn; lia).
          pose proof (rw_cells_uncut _ _ _ _ _ J1 HBR ltac:(cbn; lia)) as J2. cbn [app] in J2.
          eapply rw_cells_recell; [exact J2 | cbn; rewrite ?length_app, ?length_map; cbn; repeat split; try exact Logic.I; lia |].
          cbn [cells_bytes cbytes app]. rewrite !le2_lit, le4_lit by lia. rewrite !app_nil_r, <- ?app_assoc. cbn [app]. lazymatch goal with |- ?GG => first [reflexivity | fail 0 GG] end. }
        assert (EQSW : swap_field 4 12 (swap_field 2 8 bufdata) = pre8 ++ l1 :: l0 :: r0 :: r1 :: n3 :: n2 :: n1 :: n0 :: post).
        { rewrite Ebuf. replace 8%Z with (Z.of_nat (length pre8)) by lia. rewrite swap2_at.
          change (pre8 ++ l1 :: l0 :: r0 :: r1 :: n0 :: n1 :: n2 :: n3 :: post) with (pre8 ++ [l1; l0; r0; r1] ++ n0 :: n1 :: n2 :: n3 :: post). rewrite app_assoc.
          replace 12%Z with (Z.of_nat (length (pre8 ++ [l1; l0; r0; r1]))) by (rewrite length_app; cbn; lia). rewrite swap4_at, <- app_assoc. reflexivity. }
        rewrite EQSW.
        change (set_bufdata (pre8 ++ l1 :: l0 :: r0 :: r1 :: n3 :: n2 :: n1 :: n0 :: post) (ngc_p f qs true BS0 MINOR qb bufalloc bufdata sg i))
          with (ngc_p f qs true BS0 MINOR qb bufalloc (pre8 ++ l1 :: l0 :: r0 :: r1 :: n3 :: n2 :: n1 :: n0 :: post) sg i).
        eapply (CALL _ _ _ _ _ _ _ m6 (pre8 ++ l1 :: l0 :: r0 :: r1 :: n3 :: n2 :: n1 :: n0 :: post) (map b8 pre8 ++ [b8 l1; b8 l0; b8 r0; b8 r1; b8 n3; b8 n2; b8 n1; b8 n0] ++ bsr));
          [ symmetry; exact EQSW
          | exact MI6 | exact ST6 | exact AG6 | exact G6 | exact HD4 | exact HCUR4 | exact HTL4 | exact FRS4 | exact ERR4 | exact MG4 | exact HEB4 | exact CELLS | exact NG4
          | exact HIF6 | exact BUF6
          | change (pre8 ++ l1 :: l0 :: r0 :: r1 :: n3 :: n2 :: n1 :: n0 :: post) with (pre8 ++ [l1; l0; r0; r1; n3; n2; n1; n0] ++ post);
            replace (map b8 pre8 ++ [b8 l1; b8 l0; b8 r0; b8 r1; b8 n3; b8 n2; b8 n1; b8 n0] ++ bsr) with (map b8 pre8 ++ map b8 [l1; l0; r0; r1; n3; n2; n1; n0] ++ bsr) by reflexivity;
            apply pfx_comp; exact PFXr
          | rewrite Ebuf, !length_app; cbn [length]; lia
          | rewrite Ebuf in GRD; apply Forall_app in GRD as [GA GB]; apply Forall_app; split; [exact GA|]; do 8 (apply Forall_inv_tail in GB); repeat (constructor; [cbv beta; lia|]); exact GB ].
      + (* [comment removed for export] *)
        rewrite (eqb_lits_eq 0 0 eq_refl). cbv iota.
        eapply (CALL _ _ _ _ _ _ _ m5 bufdata bs);
          [ reflexivity | assumption | assumption | exact AG5 | exact G5 | exact HD4 | exact HCUR4 | exact HTL4 | exact FRS4 | exact ERR4 | exact MG4 | exact HEB4 | exact CELLS | exact NG4
          | exact HIF5 | exact BUF4 | exact PFX | reflexivity | exact GRD ].
  Qed.
  End Sz6.
  Lemma ngc_idb : ltac:(let t := eval cbv delta [ngc_idb__stmt] in ngc_idb__stmt in exact t).
  Proof using AI BS0R CTX FREE HFL HPL MINR P14 P16 SFL SNPRINTF. intros fuel ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' x7 m4 ps4 qb B bufalloc bufdata sg i I pad bs e cpad j0 j1 c. ltac2:(SecDiet.SzSec.closeP 'ngc_idb__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

End ChkNgC.

End WithCeil.
End F_sfpcapng_chkC.
