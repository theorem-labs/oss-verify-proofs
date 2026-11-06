(* link's program tables (LinkList.v, LinkAddr.v) against the image the build loads (Asan, fuzz_link.asan sha256
   059dae63e07c): the code table of the listing's 8289 words from fuzz_socket (0x821cc), the value table of the listing's
   base, objects and auipc values, and the listing's certificate (PAImg's pa_cert) over them, by computation. The smoke
   lemma reads fuzz_close's first instruction word at its AF_ offset in both the listing and the image. *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable LinkSyms LinkList LinkAddr.
From OSSVerify.reac_pw.fuzz_link.images Require Asan.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Definition link_lib_count : nat := 8289.
Definition linktbl : ctable :=
  Eval vm_compute in (build_table Asan.M.loaded_segments link_text link_lib_count TEmpty).
Lemma linktbl_eq : linktbl = build_table Asan.M.loaded_segments link_text link_lib_count TEmpty.
Proof. vm_cast_no_check (eq_refl linktbl). Qed.
Lemma linktbl_ok : table_ok Asan.M.loaded_segments linktbl.
Proof. rewrite linktbl_eq. apply build_table_ok0. cbv. discriminate. Qed.

Lemma link_lib_count_nslots : link_lib_count = link_nslots /\ length link_listing = link_nslots.
Proof. vm_compute. split; reflexivity. Qed.

Definition link_val (a : nat) : Z :=
  if (a =? A_TEXT)%nat then link_text else if (a <? A_HI 0)%nat then link_obj (a - A_OBJ 0) else link_hi (a - A_HI 0).

Lemma link_objs_below_hi : (A_OBJ link_nobj <= A_HI 0)%nat.
Proof. apply Nat.leb_le. vm_compute. reflexivity. Qed.

Lemma link_lib_check : pi_check lsym (clookup linktbl) link_val link_sigma link_listing = true.
Proof. vm_compute. reflexivity. Qed.

Lemma link_fuzz_close_entry :
  plookup_list lsym link_listing AF_fuzz_close = Some (PW 0x700613) /\
  clookup linktbl (link_text + AF_fuzz_close) = Some 0x700613 /\
  link_text + AF_fuzz_close = 0x8267c.
Proof. vm_compute. split; [reflexivity | split; reflexivity]. Qed.
