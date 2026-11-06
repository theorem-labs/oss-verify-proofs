(* LLVMFuzzerTestOneInput_kit_pro_agree: kit lemma K4 of the image-B walk of fuzz_transport.asan-ubsan's
   LLVMFuzzerTestOneInput (lib/B/Prog/LLVMFuzzerTestOneInput_segs.v lc_pro_agree_stmt). The model's prologue lc_pro_m
   (segs.v section 1: TOps.v LLVMFuzzerTestOneInput_m up to diginet_session_init, LLVMFuzzerTestOneInput_st.v lc_pro_eq)
   answers SPEC_OK at a world where TSim/Agree.v agree timg_B 0 holds.
   The proof replays the computation of lib/TSim/InitOk.v prologue_ok's proof (InitOk.v:163-205) at this goal, with
   InitOk's own tactics: the cursor reads (cursor), the two model calls unfolded, the writes named (wunfold_set /
   wname) and read through (wsimp_once), the 60 bytes of g_cfg as one value, the split on the desk_mac_set flag, then
   agree's clauses (pfin / vac / wlen_n / synrefl). The world stays opaque: no computation on it. It is proved for any
   timg I with timg_ok I (prologue_ok's premise) and then at timg_B (LLVMFuzzerTestOneInput_sat.v lc_timg_B_ok).
   Image B's lc_pro_m is image A's text (lib/A/Prog/LLVMFuzzerTestOneInput_kit_pro_agree.v, the template): the model
   does not depend on the image; only the timg differs. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TNeed TSess0 TCb TSess TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import Agree SimLib InitOk.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require QueueFacts.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_sat.
Import ListNotations.
Open Scope Z_scope.
Module LS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.LLVMFuzzerTestOneInput_segs.
Module LSat := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.LLVMFuzzerTestOneInput_sat.

(* The prologue at any timg the harness can run with: InitOk.v prologue_ok's script (:164-205) at lc_pro_m, without
   its size test (lc_pro_m starts below it) and without its cursor conjunct. *)
Lemma lc_pro_agree_any : forall (I : timg) (B D : list byte),
  timg_ok I -> length B = Z.to_nat W_LEN ->
  exists B25, LS.lc_pro_m I B D = Some (B25, SPEC_OK) /\ agree I 0 B25.
Proof.
  intros I B D HI HB.
  pose proof HI as [Hs Hr Hn Hno Hc24 Hpc Hcp Hpe].
  unfold LS.lc_pro_m, LS.lc_pro_scal, LS.lc_pro_minit. cbv beta zeta.
  pose proof (QueueFacts.fuzz_in_m_ok D) as Hc0.
  cursor D.
  unfold diginet_session_config_default_m. cbv zeta beta iota.
  unfold diginet_session_init_m. cbv zeta.
  bitnorm. pnorm.
  wunfold_set.
  wname.
  (repeat wsimp_once).
  (* s->cfg = *cfg (DS:64): the 60 bytes of g_cfg as one value *)
  match goal with |- context [sub ?Y OFF_g_cfg (Z.to_nat SZ_g_cfg)] =>
    assert (Hcl : length (sub Y OFF_g_cfg (Z.to_nat SZ_g_cfg)) = 60%nat)
      by (apply length_sub; [apply Z.leb_le; vm_compute; reflexivity|];
          match goal with H : length ?Y' = Z.to_nat W_LEN |- _ => wis Y' Y; rewrite H end;
          apply Z.leb_le; vm_compute; reflexivity);
    remember (sub Y OFF_g_cfg (Z.to_nat SZ_g_cfg)) as cfg eqn:Ecfg
  end.
  pconst. zdec.
  match goal with |- context [(?x / 4) mod 2 =? 0] => destruct (Z.eqb_spec ((x / 4) mod 2) 0) as [Hds|Hds] end.
  all: cbv beta iota; zdec.
  all: wunfold_set.
  all: wname.
  all: eexists _; split; [reflexivity|].
  all: constructor; [constructor|..].
  all: try (lazymatch goal with |- timg_ok _ => exact HI end).
  all: try (lazymatch goal with |- length _ = Z.to_nat W_LEN => wlen_n end).
  all: try (lazymatch goal with |- agree_cfg _ => constructor end; try pfin).
  all: try (lazymatch goal with |- agree_io _ _ => constructor end; try pfin).
  all: try (lazymatch goal with |- agree_st _ => constructor end; try pfin).
  all: try (lazymatch goal with |- agree_fly _ => constructor end; try vac; try pfin).
  all: try (lazymatch goal with |- agree_time _ _ => constructor end; try pfin).
  all: try (lazymatch goal with |- agree_misc _ _ => constructor end; try pfin).
  all: try (lazymatch goal with |- c2_keepalive _ => pfin end).
  all: try (lazymatch goal with |- g_rx _ = 0 => pfin end).
  all: try (lazymatch goal with |- agree_q _ _ => constructor end; try pfin).
  (* A2 (DS:64): the copy is the 60 bytes of g_cfg *)
  all: try (lazymatch goal with |- sub _ A_S_cfg_host_mac 60 = sub _ OFF_g_cfg 60 =>
              repeat wsimp_once; rewrite Ecfg; change (Z.to_nat SZ_g_cfg) with 60%nat; synrefl end).
Qed.

(* K4 *)
Lemma lc_pro_agree_ok : LS.lc_pro_agree_stmt.
Proof.
  unfold LS.lc_pro_agree_stmt. intros Bw0 D HB _.
  exact (lc_pro_agree_any _ Bw0 D LSat.lc_timg_B_ok HB).
Qed.
