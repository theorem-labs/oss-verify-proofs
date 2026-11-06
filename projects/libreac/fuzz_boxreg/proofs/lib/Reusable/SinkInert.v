(* Relocated (module paths only, fuzz_grant -> fuzz_boxreg) from a working branch add754d0ac894a150d46cda285beee12e53605e3
   proofs/libreac/fuzz_grant/lib/Reusable/SinkInert.v (a Theorem Labs lane's SinkInert, SHARED-WALKS.md row 29). *)
(* Image-generic (no image numeral, no unit name): cgif's sink path YI16.sink_path ("/tmp/out.gif") is inert in any
   harness that writes no file. cgif's literal stays in the shared kit; such a unit discharges it with these lemmas.
   - sink_std_fds: the three standard channels name no file, so none names the sink path.
   - sink_inert md fs: no fd names the sink path and the file system is fs. sink_inert_std gives it at the driver's
     start (the standard channels only); sink_inert_of_inv gives it from a unit's OWN driver loop invariant that
     carries the two conjuncts (fuzz_reply: A/AD1w.v MDI). Keeping it across the run is that invariant's job.
   - sinkn_os_kept: an OS step whose footprint leaves the sink closed (YCbq.aos_step, ~ YI16.sink_open_fp) keeps any
     sink invariant that reads the model only through same_io; asink_none_os_kept segs K is its instance at cgif's sink
     invariant YE00.asink_none, the discharge of H_SINK_INERT_A / H_SINK_INERT_B for a core whose SINKN is
     asink_none segs K (fuzz_boxreg: box_segs / boxb_segs and the core's tfib_K). They use only the closed arm of
     aos_step (YCbq.aos_step_closed): m_fd and m_fsys do not change.
   CONDITION: a unit whose program can OPEN a path equal to sink_path (for example an fopen of a name taken from the
   input) must first show that its invariant excludes that open. Inv in sink_inert_of_inv, and the premise
   ~ YI16.sink_open_fp FP of the step lemmas, must not be premises that are false on some run. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Namei.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YI16 YG0d YCbq YE00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YA0e.
Open Scope Z_scope.

Lemma sink_std_fds : Namei.fd_names_path YA0e.APSG.fds_std YI16.sink_path = false.
Proof. vm_compute. reflexivity. Qed.

Definition sink_inert (md : Model) (fs : Fs.Fs) : Prop :=
Namei.fd_names_path (m_fds md) YI16.sink_path = false /\ m_fs md = fs.

Lemma sink_inert_std : forall md, m_fds md = YA0e.APSG.fds_std -> sink_inert md (m_fs md).
Proof. intros md E. split; [rewrite E; exact sink_std_fds | reflexivity]. Qed.

Lemma sink_inert_of_inv : forall (Inv : Model -> Fs.Fs -> Prop),
(forall md fs, Inv md fs -> Namei.fd_names_path (m_fds md) YI16.sink_path = false) ->
(forall md fs, Inv md fs -> m_fs md = fs) ->
forall md fs, Inv md fs -> sink_inert md fs.
Proof. intros Inv H1 H2 md fs H. split; [exact (H1 md fs H) | exact (H2 md fs H)]. Qed.

Lemma sinkn_os_kept : forall (SINKN : (word -> option byte) -> Model -> Prop),
(forall m md md', same_io md md' -> SINKN m md -> SINKN m md') ->
forall (FP : list (Z * Z)) (md md' : Model) (m : word -> option byte),
~ YI16.sink_open_fp FP -> aos_step FP md md' -> SINKN m md -> SINKN m md'.
Proof. intros SINKN HS FP md md' m Hcl Hos H. exact (HS m md md' (aos_step_closed_same_io FP md md' Hcl Hos) H). Qed.

Section n.
Variable segs : list Segment.
Variable K : asink_syms.
Lemma asink_none_same_io : forall m md md', same_io md md' -> asink_none segs K m md -> asink_none segs K m md'.
Proof.
intros m md md' (Efd & _ & _ & _) (Henv & Hhead & Hn).
split; [exact Henv|]. split; [exact Hhead|]. unfold m_fds in *. rewrite Efd. exact Hn.
Qed.
Lemma asink_none_os_kept : forall (FP : list (Z * Z)) (md md' : Model) (m : word -> option byte),
~ YI16.sink_open_fp FP -> aos_step FP md md' -> asink_none segs K m md -> asink_none segs K m md'.
Proof. exact (sinkn_os_kept (asink_none segs K) asink_none_same_io). Qed.
End n.
