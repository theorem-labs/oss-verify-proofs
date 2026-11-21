(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode Tac InitMem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import STree AsanCtrl AsanEmbed AsanCtrlProps.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW Require Import AImg AProto ABase AKit ARep F_apoison APoisonR_iface F_rsrvshadow AFrameD.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Local Lemma highD : forall W, Forall (fun iv : Z * Z => AIMG_HI <= fst iv) W -> forall A n, A + n <= AIMG_HI -> disjoint_from W A n.
Proof. intros W HW A n HA. induction HW as [|[lo hi] W H1 H2 IH]; cbn in *; [exact I|]. split; [lia| apply IH]. Qed.
Local Lemma poison_cells_high : forall W m m', poison_cells m -> munch W m m' -> Forall (fun iv : Z * Z => AIMG_HI <= fst iv) W -> poison_cells m'.
Proof.
  intros W m m' (P1 & P2 & P3 & P4 & P5 & P6 & P7) MU HW. pose proof (highD W HW) as D. unfold AIMG_HI in D. unfold poison_cells.
  repeat lazymatch goal with |- _ /\ _ => split end;
    (eapply cells_frameD; [eassumption | exact MU | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply D; lia]).
Qed.
Local Lemma premap_cells_high : forall W m m', premap_cells m -> munch W m m' -> Forall (fun iv : Z * Z => AIMG_HI <= fst iv) W -> premap_cells m'.
Proof.
  intros W m m' (P1 & P2 & P3 & P4 & P5 & P6 & P7) MU HW. pose proof (highD W HW) as D. unfold AIMG_HI in D. unfold premap_cells.
  repeat lazymatch goal with |- _ /\ _ => split end;
    first [ apply premap_canary_any
          | (eapply cells_frameD; [eassumption | exact MU | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply D; lia]) ].
Qed.

Theorem poison_remap_proof : poison_remap_stmt.
Proof.
  unfold poison_remap_stmt.
  intros R k Q RNG. intros until junk. intros ST CEIL LO MI PC PRC RR -> -> -> AL SL SZ HI HE BIG DST RIMG RSTK RSH KONT.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). word_range sp SPR. unfold PZR_STACK in *.
  pose proof HI as HI'. unfold ablk, AIMG_HI, KLS in HI'. pose proof atop_range as ATR.
  assert (SHR : 0x800c7c00 <= shad addr /\ shad addr + shlen size <= 0x10007fff8000 /\ 0 < shlen size).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by (clear; lia). change (2^3) with 8. clear -AL SL SZ HI' HE ATR. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  change (poison0 addr size k) with k.
  iprefix.
  eapply evtF_cut.
  { eapply (poison_shadow_spec RNG) with (addr := addr) (size := size) (v := 0) (lo := lo); try eassumption; try reflexivity.
    all: try (clear -CEIL LO LO0 SPR AL SL SZ HI HI' HE ATR; first [exact HI | lia]).
    intros _. unfold shlen. rewrite Z.shiftr_div_pow2 by (clear; lia). clear -SZ HE HI' ATR. Z.div_mod_to_equations. lia. }
  cbv beta. intros ms' PO. unfold poison_post in PO. destruct_exs PO. destruct PO as (-> & MUp & WMp & MIp & STp & SHZ).
  apply evtF_done. eapply KONT. unfold premap_post, PZR_STACK.
  split; [apply fp_le_refl|].
  split; [intros BW; exact BW|].
  split. { eapply munch_weaken; [| exact MUp]. intros xq Hq. cbn in Hq |- *. clear -Hq. lia. }
  split; [exact WMp|]. split; [exact MIp|]. split; [exact STp|].
  split. { unfold zeros. rewrite ?unsigned_lit in SHZ by (clear; lia). exact SHZ. }
  split; [exact RSH|].
  split; [eapply poison_cells_high; [exact PC | exact MUp |] | eapply premap_cells_high; [exact PRC | exact MUp |]];
    (repeat (apply Forall_cons; [cbn; unfold AIMG_HI; clear -CEIL LO SPR SHR; lia|]); apply Forall_nil).
Qed.
Definition poison_remap : poison_remap_stmt := poison_remap_proof.
End CANSEC1.
