(** * openssl / acert: characterisation problems

    These are not claims.  Each is a property of a classifier program [C], which
    is any static riscv64 Linux executable you supply, and of a bound [b].  A
    result is a [C] with a proof of [<build>_classifies C] and of
    [<build>_classifier_rejects_at_most C b] for as small a [b] as you can.
    Together with [image_wf C] such a result proves
    [Statements.<build>_agreement_decidable], and (through
    [Shapes.disagrees_at_most_of_classifier])
    [Statements.<build>_disagrees_at_most b]. *)

From Stdlib Require Import QArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.openssl.acert Require Images Distribution.

(** [C] exits 0 exactly on the finite inputs where the plain and ASan builds
    agree, and 1 on the others. *)
Definition asan_classifies (C : Image) : Prop :=
  classifies Env.alloc_forced_only Images.plain Images.asan C.

(** Under [Distribution.w], the inputs [C] rejects weigh at most [b]. *)
Definition asan_classifier_rejects_at_most (C : Image) (b : Q) : Prop :=
  classifier_rejects_at_most C Distribution.w Distribution.M b.

(** [C] exits 0 exactly on the finite inputs where the plain and UBSan builds
    agree, and 1 on the others. *)
Definition ubsan_classifies (C : Image) : Prop :=
  classifies Env.alloc_forced_only Images.plain Images.ubsan C.

(** Under [Distribution.w], the inputs [C] rejects weigh at most [b]. *)
Definition ubsan_classifier_rejects_at_most (C : Image) (b : Q) : Prop :=
  classifier_rejects_at_most C Distribution.w Distribution.M b.

(** [C] exits 0 exactly on the finite inputs where the plain and ASan+UBSan
    builds agree, and 1 on the others. *)
Definition asan_ubsan_classifies (C : Image) : Prop :=
  classifies Env.alloc_forced_only Images.plain Images.asan_ubsan C.

(** Under [Distribution.w], the inputs [C] rejects weigh at most [b]. *)
Definition asan_ubsan_classifier_rejects_at_most (C : Image) (b : Q) : Prop :=
  classifier_rejects_at_most C Distribution.w Distribution.M b.
