(* Theorem Labs, 2026-10-30 (a Theorem Labs lane, for a Theorem Labs lane's cf layer round 3 at plugin-hostd/fuzz_reply).
   rule 24: no function proved (kind: image rows; closed facts about reply's image B, fuzz_reply.asan-ubsan, pin
   10ffb5f9202a; no function walk).

   Image B's twin of A/ReplyImg_pfrows.v: the two unit rows round 3's ARcf_nil_init (Reusable/YGcfNilInit.v:100-101)
   takes at the image's symbol facts:
   - errb_ial_apart_reply_B: the layer's errb_ial_apart_t (Reusable/YG0ncf.v:160): the error-message-buffer object
     [cf_errbuf_obj, + 56) lies below the internal allocator's arena (TFIB_IAL_LO) and so outside the arena and its
     flag (TFIB_IAL_FLAG).
   - pf_cells_owned_reply_B: the layer's pf_cells_owned_t (Reusable/YG0ncf.v:207) = pf_cells_static_t /\
     pf_ial_apart_t. The static half is pf_cells_static_reply_B below: the toolname cell lies in the first region of
     Tfib_owned_static, the pfcb cell in the fifth, and both lie outside the instance object [TFIB_INST,
     + kInstObjSize). The arena half is a Theorem Labs lane's ReplyRelroGeoB.pf_ial_apart_reply_B, cited.
   Every bound is a NAME: the CfImg_B fields (B/CfImgB.v), the TfibSyms constants and Tfib_owned_static of B/YF0m.v,
   and YG0ncf.kInstObjSize. The owned regions are computed (vm_compute of nth over Tfib_owned_static), not retyped. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP09 YG0f YGcfNames.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0n YG0ncf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YF0m CfImgB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyRelroGeoB.
Open Scope Z_scope.

(* Image B's CfImg for the texts below, as B/CfRBridgeRulesB.v takes it. *)
#[local] Existing Instance CfImg_B.

(* errb_ial_apart_t at TfibSyms. *)
Lemma errb_ial_apart_reply_B : forall B, TfibSyms B -> YG0ncf.errb_ial_apart_t (ci := CfImg_B) B.
Proof.
intros B TS a Ha. rewrite (ts_ial_lo B TS), (ts_ial_hi B TS), (ts_ial_flag B TS).
cbn [cf_errbuf_obj CfImg_B] in Ha. unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG. lia.
Qed.

(* pf_cells_static_t at TfibSyms: the toolname cell in owned region 0, the pfcb cell in owned region 4. *)
Lemma pf_cells_static_reply_B : forall B, TfibSyms B -> YG0ncf.pf_cells_static_t (ci := CfImg_B) B.
Proof.
intros B TS a Ha. rewrite (ts_owned B TS), (ts_inst B TS).
cbn [cf_toolname_cell cf_pfcb_cell CfImg_B] in Ha. split.
- apply Exists_exists. destruct Ha as [Ha | Ha].
  + exists (nth 0 Tfib_owned_static (0, 0)). split; [apply nth_In; vm_compute; lia |].
    remember (nth 0 Tfib_owned_static (0, 0)) as r eqn:Er. vm_compute in Er. subst r.
    unfold YG0n.in_zr. cbn [fst snd]. lia.
  + exists (nth 4 Tfib_owned_static (0, 0)). split; [apply nth_In; vm_compute; lia |].
    remember (nth 4 Tfib_owned_static (0, 0)) as r eqn:Er. vm_compute in Er. subst r.
    unfold YG0n.in_zr. cbn [fst snd]. lia.
- unfold TFIB_INST, YG0ncf.kInstObjSize. lia.
Qed.

(* pf_cells_owned_t at TfibSyms: the static half above and the arena half of ReplyRelroGeoB. *)
Lemma pf_cells_owned_reply_B : forall B, TfibSyms B -> YG0ncf.pf_cells_owned_t (ci := CfImg_B) B.
Proof.
intros B TS. unfold YG0ncf.pf_cells_owned_t.
split; [exact (pf_cells_static_reply_B B TS) | exact (ReplyRelroGeoB.pf_ial_apart_reply_B B TS)].
Qed.
