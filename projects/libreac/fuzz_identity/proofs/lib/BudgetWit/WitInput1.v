(* Theorem Labs, 2026-11: the one-byte-file input of libreac/fuzz_identity's ASan fuzz-path witness (OSSV-265); made from projects/curl/fuzz_fnmatch/proofs/lib/BudgetWit/WitInput.v with its file shortened to one byte and its entry taken at fuzz_identity's ASan image. *)
From Stdlib Require Import ZArith List Lia.
From stdpp.bitvector Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs MemImageType StackLayout State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei Open.
From OSSVerify.Core Require Premises.
From OSSVerify.libreac.fuzz_identity Require Images.
Import ListNotations.
Open Scope Z_scope.

(** * The input of the argc = 2 witness: one file of one byte

    [argv = [[]; "in"]] (argc = 2, the driver's file branch) over a file
    system that holds the one file ["in"] with the one byte 0.  The driver
    ([Reusable.YO05.driver_m]) mallocs its 65536-byte buffer (ASan's secondary
    allocator, the growth path), reads the byte, finds [dlen = 1 < HDR_MIN = 6],
    frees the buffer, writes its short-input message and exits: it does not
    reach [LLVMFuzzerTestOneInput].

    [wit_input1] is built the way [OSSVerify.Core.Premises.witness_input]
    builds its own ([mkProcInput] with end of input, ids 0, a quiet network,
    the default descriptor limit, an empty signal mask, [hwcap_rv64gc], no
    abort declaration and Sv48); it differs from that one only in argv and in
    the file system.  105 and 110 are the bytes of the name "in" this witness
    chooses; 4096 is Linux's [PATH_MAX]. *)

Definition wit_path : list byte := [Z_to_bv 8 105; Z_to_bv 8 110].

(** The witness file's contents: one zero byte. *)
Definition wit_data1 : list byte := [Z_to_bv 8 0].

Definition wit_input1 : ProcInput :=
  mkProcInput [[]; wit_path] [] [(wit_path, wit_data1)] IEof (Z_to_bv 64 0) (Z_to_bv 64 0) []
    net_silent default_nofile (Z_to_bv 64 0) hwcap_rv64gc false Sv48.

Lemma wit_path_no_nul : ~ In (Z_to_bv 8 0) wit_path.
Proof.
  unfold wit_path. intros [H | [H | []]];
    apply (f_equal bv_unsigned) in H; vm_compute in H; discriminate H.
Qed.

Lemma wit_path_relative : key_is_relative wit_path.
Proof.
  change (Z_to_bv 8 105 <> path_slash_byte). unfold path_slash_byte.
  intros H. apply (f_equal bv_unsigned) in H. vm_compute in H. discriminate H.
Qed.

Lemma wit_valid_argv : valid_argv [[]; wit_path].
Proof.
  unfold valid_argv.
  split; [split; apply Z.leb_le; vm_compute; reflexivity |].
  split; [apply Z.leb_le; vm_compute; reflexivity |].
  split.
  { apply Forall_cons; [apply Z.leb_le; vm_compute; reflexivity |].
    apply Forall_cons; [apply Z.leb_le; vm_compute; reflexivity | apply Forall_nil]. }
  split.
  { apply Forall_cons; [intros [] |].
    apply Forall_cons; [exact wit_path_no_nul | apply Forall_nil]. }
  cbn [tl]. apply Forall_cons; [split; vm_compute; reflexivity | apply Forall_nil].
Qed.

Lemma wit_valid_envp : valid_envp [].
Proof.
  unfold valid_envp.
  split; [apply Z.leb_le; vm_compute; reflexivity |].
  split; [apply Z.leb_le; vm_compute; reflexivity |].
  split; apply Forall_nil.
Qed.

Lemma wit_valid_fs : valid_fs [(wit_path, wit_data1)].
Proof.
  unfold valid_fs. split; [vm_compute; reflexivity |].
  apply Forall_cons; [exact wit_path_no_nul | apply Forall_nil].
Qed.

Lemma wit_fs_keys_relative : fs_keys_relative (in_image_fs wit_input1).
Proof.
  unfold fs_keys_relative. apply Forall_cons; [exact wit_path_relative | apply Forall_nil].
Qed.

(** The input is valid: [asan_halts]'s premise [valid_input] holds at it, so
    the witness below is not about an empty set of inputs. *)
Lemma wit_valid_input1 : valid_input wit_input1.
Proof.
  unfold valid_input.
  refine (conj wit_valid_argv (conj wit_valid_envp (conj wit_valid_fs (conj wit_fs_keys_relative
    (conj _ (conj _ (conj _ (conj _ (conj _ (conj eq_refl (conj eq_refl
    (conj _ (conj _ (conj eq_refl (conj eq_refl _))))))))))))))).
  - vm_compute. reflexivity.
  - unfold valid_creds, valid_id. split; apply Z.ltb_lt; vm_compute; reflexivity.
  - unfold valid_nofile. apply Z.leb_le. vm_compute. reflexivity.
  - unfold valid_sigmask. apply bv_eq. vm_compute. reflexivity.
  - unfold valid_hwcap. left. reflexivity.
  - unfold valid_urandom. exact State.default_urandom_infinite.
  - (* LPS 727298f3: [Run.valid_launch]; the input's exec file name is [State.default_execfn], the
       one-byte relative name "a", and the launch is far under the E2BIG limit. *)
    unfold valid_launch, wit_input1, mkProcInput. cbn [in_execfn]. split;
      [ unfold valid_execfn, valid_path_name, default_execfn; left; split;
        [ cbn; lia
        | cbn; intros [Hz | []]; apply (f_equal bv_unsigned) in Hz; vm_compute in Hz; discriminate ]
      | unfold e2big_limit; apply Z.leb_le; vm_compute; reflexivity ].
  - reflexivity.
Qed.

Lemma wit_argv1 : in_argv wit_input1 = [[]; wit_path].
Proof. reflexivity. Qed.

Lemma wit_path_length : (length wit_path < 4096)%nat.
Proof. apply Nat.ltb_lt. vm_compute. reflexivity. Qed.

Lemma wit_path_ne_nil : wit_path <> [].
Proof. unfold wit_path. discriminate. Qed.

Lemma wit_path_plain : openat_plain_name wit_path = true.
Proof. vm_compute. reflexivity. Qed.

Lemma wit_path_ne_dot : wit_path <> dot_path.
Proof. unfold wit_path, dot_path. intros H. discriminate H. Qed.

(** The file [argv[1]] names holds exactly one byte. *)
Lemma wit_fs_lookup1 : fs_lookup (in_fs wit_input1) wit_path = Some wit_data1.
Proof. vm_compute. reflexivity. Qed.

Lemma wit_data1_length : length wit_data1 = 1%nat.
Proof. reflexivity. Qed.

(** The entry premise at fuzz_identity's ASan image. *)
Lemma wit_entry1 : exists en, valid_entry OSSVerify.libreac.fuzz_identity.Images.asan en wit_input1.
Proof.
  exact (Premises.valid_input_entry OSSVerify.libreac.fuzz_identity.Images.asan wit_input1
    OSSVerify.libreac.fuzz_identity.Images.asan_wf wit_valid_input1).
Qed.
