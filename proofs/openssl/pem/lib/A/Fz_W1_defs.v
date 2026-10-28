(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac Arr.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_agree Fz_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).

Definition e_mem_write : Z := 0x3040d4.
Definition e_mem_read : Z := 0x30431c.
Definition e_mem_puts : Z := 0x304534.
Definition e_mem_gets : Z := 0x3045a8.
Definition e_mem_ctrl : Z := 0x3047ac.
Definition e_mem_new : Z := 0x304d94.
Definition e_mem_free : Z := 0x304db8.
Definition e_mem_buf_sync : Z := 0x304e74.
Definition e_mem_buf_free : Z := 0x30508c.
Definition e_mem_init : Z := 0x3051e4.
Definition e_secmem_new : Z := 0x305408.
Definition e_BUF_MEM_new_ex : Z := 0x249d5c.
Definition e_BUF_MEM_free : Z := 0x249e04.
Definition e_BUF_MEM_grow_clean : Z := 0x24a224.
Definition e_sec_alloc_realloc : Z := 0x24a124.
Definition e_BIO_s_mem : Z := 0x303e8c.
Definition e_BIO_s_secmem : Z := 0x303eb4.
Definition e_BIO_clear_flags : Z := 0x236d00.
Definition e_BIO_set_flags : Z := 0x236d60.
Definition M_MEM_A : Z := 0x548280.             (* [comment removed for export] *)
Definition M_SECMEM_A : Z := 0x548320.
Definition msec (meth : Z) : Z := if meth =? M_SECMEM_A then 1 else 0.

(* [comment removed for export] *)
Definition bufmem_cells (len data max : Z) (flw : word) : list cell := [C8 (wz len); C8 (wz data); C8 (wz max); C8 flw].
Definition readp_cells (len D off : Z) (rmaxw flw : word) : list cell := [C8 (wz (len - off)); C8 (wz (D + off)); C8 rmaxw; C8 flw].
(* [comment removed for export] *)
Definition bio_w1_cells (iw shw : word) (fl : Z) (rrw numw padw ptrw : word) : list cell := [C4 iw; C4 shw; C4 (wz fl); C4 rrw; C4 numw; C4 padw; C8 ptrw].
Definition fl_ok (fl : Z) : Prop := 0 <= fl < 2 ^ 31 /\ Z.land fl 512 = 0.
(* [comment removed for export] *)
Definition bio_head (meth : Z) : list cell := [C8 (wz 0); C8 (wz meth); C8 (wz 0); C8 (wz 0); C8 (wz 0)].
Definition bio_tail (nr nw : word) : list cell := [C8 (wz 0); C8 (wz 0); C4 (wz 1); C4 (wz 0); C8 nr; C8 nw; C8 (wz 0); C8 (wz 0)].

(* [comment removed for export] *)
Definition mb_innerA (live : list (Z * Z)) (m : mem) (BB BM RP len max off : Z) (flw blw : word) (D : option Z) : Prop :=
  exists rmaxw : word,
     In (BB, 16) live /\ BB mod 16 = 0 /\ rw_cells asegs m BB [C8 (wz BM); C8 (wz RP)] /\ In (BM, 32) live /\ BM mod 16 = 0 /\ In (RP, 32) live /\ RP mod 16 = 0
  /\ 0 <= off <= len /\ len <= max /\ max < 2 ^ 31 - 1
  /\ match D with
     | None => max = 0 /\ rw_cells asegs m BM [C8 blw; C8 (wz 0); C8 (wz 0); C8 flw] /\ rw_cells asegs m RP (readp_cells 0 0 0 rmaxw flw)
     | Some d => exists junk, In (d, max) live /\ 0 < max /\ rw_cells asegs m BM [C8 blw; C8 (wz d); C8 (wz max); C8 flw]
                 /\ rw_cells asegs m RP (readp_cells len d off rmaxw flw) /\ length junk = Z.to_nat max /\ rw_cells asegs m d [CB (Z.to_nat max) junk]
     end.
(* [comment removed for export] *)
Definition mbio_blocksA (BI BB BM RP : Z) (D : option Z) : list Z := [BI; BB; BM; RP] ++ match D with Some d => [d] | None => [] end.
(* [comment removed for export] *)
Definition mbio_repxA (live : list (Z * Z)) (m : mem) (BI BM : Z) (blw : word) (meth len max off : Z) (D : option Z) : Prop :=
  exists (BB RP fl : Z) (rrw padw nr nw : word),
     In (BI, 128) live /\ BI mod 16 = 0 /\ List.NoDup (mbio_blocksA BI BB BM RP D) /\ (meth = M_MEM_A \/ meth = M_SECMEM_A)
  /\ rw_cells asegs m BI (bio_head meth) /\ rw_cells asegs m (BI + 40) (bio_w1_cells (wz 1) (wz 1) fl rrw (wz 4294967295) padw (wz BB)) /\ fl_ok fl
  /\ rw_cells asegs m (BI + 72) (bio_tail nr nw) /\ mb_innerA live m BB BM RP len max off (wz (msec meth)) blw D.
Definition mbio_repA (live : list (Z * Z)) (m : mem) (BI meth len max off : Z) (D : option Z) : Prop :=
  exists BM, mbio_repxA live m BI BM (wz len) meth len max off D.

(* [comment removed for export] *)
Lemma live_ne_apart : forall RT (AF : art_facts RT) (Σ : rts RT) (m : mem) p1 n1 p2 n2,
  ART RT Σ m -> In (p1, n1) (rt_live RT Σ) -> In (p2, n2) (rt_live RT Σ) -> (p1, n1) <> (p2, n2) -> p1 + n1 <= p2 \/ p2 + n2 <= p1.
Proof.
  intros RT AF Σ m p1 n1 p2 n2 HA H1 H2 NE. destruct (in_split _ _ H1) as (l1 & l2 & EL).
  assert (H2' : In (p2, n2) (l1 ++ l2)).
  { rewrite EL in H2. apply in_app_or in H2. apply in_or_app. destruct H2 as [X|[X|X]]; [left; exact X | exfalso; exact (NE X) | right; exact X]. }
  exact (af_live_disj RT AF Σ m p1 n1 p2 n2 l1 l2 HA EL H2').
Qed.
