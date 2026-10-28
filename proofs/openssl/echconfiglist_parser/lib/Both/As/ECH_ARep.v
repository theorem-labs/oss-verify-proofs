(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr SysStep CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsCXXHeap ECH_AImg ECH_Xpres.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.
  Variable HI : asr.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint in_ivs_b (X : list (Z * Z)) (a : Z) : bool :=
  match X with [] => false | iv :: X' => ((fst iv <=? a) && (a <? snd iv)) || in_ivs_b X' a end.
Lemma in_ivs_b_spec : forall X a, in_ivs_b X a = true <-> rin_ivs X a.
Proof.
  induction X as [|[lo hi] X IH]; intros a; cbn; [split; [discriminate| tauto]|].
  rewrite Bool.orb_true_iff, Bool.andb_true_iff, Z.leb_le, Z.ltb_lt, IH. tauto.
Qed.

(* [comment removed for export] *)
Definition oblk : Type := option (bptr * Z).      (* [comment removed for export] *)
Definition ofield (LB : list block) (P : Z) (o : oblk) : Prop :=
  match o with
  | None => P = 0
  | Some (id, n) => 0 < P /\ 0 <= n /\ In (id, P, n) LB
  end.
Definition blocks_of (P : Z) (o : oblk) : list block :=
  match o with None => [] | Some (id, n) => [(id, P, n)] end.

Lemma ofield_LB_mono : forall LB LB' P o, ofield LB P o -> (forall b, In b LB -> In b LB') -> ofield LB' P o.
Proof. intros LB LB' P [[id n]|] H HL; cbn in *; [| exact H]. destruct H as (H1 & H2 & H3). auto. Qed.

(* [comment removed for export] *)
Definition off_image (a n : Z) : Prop := a + n <= IMG_LO \/ IMG_HI <= a.
Definition outcell_ok (LB : list block) (SP B a : Z) : Prop :=
  aclient_range HI LB SP a 8 /\ off_image a 8 /\ a + 8 <= B.

(* [comment removed for export] *)
Definition zeros (n : nat) : list byte := repeat (b8 0) n.
Lemma zeros_length : forall n, length (zeros n) = n. Proof. intros n. apply repeat_length. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pk_cells (cur ms rem : Z) : list cell := [C8 (wz cur); C8 (wz ms); C8 (wz rem)].
Definition pk_in (base len cur rem : Z) : Prop := base <= cur /\ 0 <= rem /\ cur + rem <= base + len.

Lemma pk_in_forward : forall base len cur rem k,
  pk_in base len cur rem -> 0 <= k <= rem -> pk_in base len (cur + k) (rem - k).
Proof. unfold pk_in. lia. Qed.
Lemma pk_in_sub : forall base len cur rem k,
  pk_in base len cur rem -> 0 <= k <= rem -> pk_in base len cur k.
Proof. unfold pk_in. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record skrep := mkSK {
  sk_elems : list Z ;      (* [comment removed for export] *)
  sk_data : Z ;            (* [comment removed for export] *)
  sk_cap : Z ;             (* [comment removed for export] *)
  sk_sorted : Z ;
  sk_comp : Z ; sk_cmp_thunk : Z ; sk_free_thunk : Z ; sk_copy_thunk : Z ;
  sk_id : bptr ;           (* [comment removed for export] *)
  sk_did : bptr            (* [comment removed for export] *) }.

Definition sk_num (K : skrep) : Z := zlength (sk_elems K).
Definition O_SK_DATA : Z := 8.  Definition O_SK_SORTED : Z := 16.  Definition O_SK_CAP : Z := 20.
Definition O_SK_COMP : Z := 24. Definition O_SK_CMPTH : Z := 32.   Definition O_SK_FREETH : Z := 40.  Definition O_SK_COPYTH : Z := 48.
Definition SK_SIZE : Z := 56.

Definition sk_hdr_cells (K : skrep) (pad : list byte) : list cell :=
  [C4 (wz (sk_num K)); CB 4 pad; C8 (wz (sk_data K)); C4 (wz (sk_sorted K)); C4 (wz (sk_cap K));
   C8 (wz (sk_comp K)); C8 (wz (sk_cmp_thunk K)); C8 (wz (sk_free_thunk K)); C8 (wz (sk_copy_thunk K))].

Definition SKobj (LB : list block) (m : mem) (a : Z) (K : skrep) : Prop :=
  (exists pad, length pad = 4%nat /\ rw_cells asegs m a (sk_hdr_cells K pad))
  /\ 0 < a /\ In (sk_id K, a, SK_SIZE) LB
  /\ 0 <= sk_num K <= sk_cap K /\ sk_cap K <= 2^20 /\ 0 <= sk_sorted K <= 1
  /\ Forall (fun p => 0 < p < 2^64) (sk_elems K)
  /\ ( (sk_cap K = 0 /\ sk_data K = 0)
     \/ (4 <= sk_cap K /\ 0 < sk_data K /\ (a + SK_SIZE <= sk_data K \/ sk_data K + 8 * sk_cap K <= a)
         /\ In (sk_did K, sk_data K, 8 * sk_cap K) LB
         /\ u64arr asegs m (sk_data K) (map wz (sk_elems K))
         /\ exists junk, rw_cells asegs m (sk_data K + 8 * sk_num K) [CB (Z.to_nat (8 * (sk_cap K - sk_num K))) junk]) ).

Definition blocks_SK (a : Z) (K : skrep) : list block :=
  (sk_id K, a, SK_SIZE) :: (if sk_cap K =? 0 then [] else [(sk_did K, sk_data K, 8 * sk_cap K)]).
(* [comment removed for export] *)
Definition SK_foot (a : Z) (K : skrep) : list (Z * Z) :=
  (a, a + SK_SIZE) :: (if sk_cap K =? 0 then [] else [(sk_data K, sk_data K + 8 * sk_cap K)]).

(* [comment removed for export] *)
Definition sk_fresh (c : Z) (id did : bptr) : skrep := mkSK [] 0 0 1 c 0 0 0 id did.

(* [comment removed for export] *)
Definition sk_grow (cap : Z) : Z := cap * 8 / 5.

Lemma SKobj_LB_mono : forall LB LB' m a K, SKobj LB m a K -> (forall b, In b LB -> In b LB') -> SKobj LB' m a K.
Proof.
  intros LB LB' m a K H HL. unfold SKobj in *.
  destruct H as (H1 & H0 & H2 & H3 & H4 & H5 & H6 & H9).
  split; [exact H1|]. split; [exact H0|]. split; [auto|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact H6|].
  destruct H9 as [H9|(C1 & C2 & C3 & C4 & C5 & C6)]; [left; exact H9| right]. auto 7.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record bufrep := mkBUF { bm_len : Z; bm_data : Z; bm_max : Z; bm_flags : Z }.
Definition buf_cells (B : bufrep) : list cell :=
  [C8 (wz (bm_len B)); C8 (wz (bm_data B)); C8 (wz (bm_max B)); C8 (wz (bm_flags B))].
Definition BUFMEM_SIZE : Z := 32.

Record biorep := mkBIO {
  bio_method : Z; bio_init : Z; bio_shutdown : Z; bio_flags : Z; bio_retry : Z; bio_numf : Z;
  bio_ptr : Z; bio_next : Z; bio_prev : Z; bio_refs : Z; bio_nread : Z; bio_nwrite : Z }.
Definition O_BIO_METHOD : Z := 8.  Definition O_BIO_INIT : Z := 40.  Definition O_BIO_FLAGS : Z := 48.
Definition O_BIO_PTR : Z := 64.    Definition O_BIO_NEXT : Z := 72.  Definition O_BIO_REFS : Z := 88.
Definition O_BIO_NREAD : Z := 96.  Definition O_BIO_EXDATA : Z := 112.
Definition BIO_SIZE : Z := 128.
(* [comment removed for export] *)
Definition bio_cells (B : biorep) : list cell :=
  [C8 (wz 0); C8 (wz (bio_method B)); C8 (wz 0); C8 (wz 0); C8 (wz 0);
   C4 (wz (bio_init B)); C4 (wz (bio_shutdown B)); C4 (wz (bio_flags B)); C4 (wz (bio_retry B));
   C4 (wz (bio_numf B)); C4 (wz 0); C8 (wz (bio_ptr B)); C8 (wz (bio_next B)); C8 (wz (bio_prev B));
   C4 (wz (bio_refs B)); C4 (wz 0); C8 (wz (bio_nread B)); C8 (wz (bio_nwrite B)); C8 (wz 0); C8 (wz 0)].

(* [comment removed for export] *)
Definition O_METH_BREAD : Z := 32.
Definition METH_mem (m : mem) : Prop :=
  rw_cells asegs m (A_mem_buf_method + O_METH_BREAD)
    [C8 (wz P_bread_conv); C8 (wz P_mem_read); C8 (wz P_mem_puts); C8 (wz P_mem_gets); C8 (wz P_mem_ctrl);
     C8 (wz P_mem_new); C8 (wz P_mem_free); C8 (wz 0)].
Definition METH_b64 (m : mem) : Prop :=
  rw_cells asegs m (A_b64_method + O_METH_BREAD)
    [C8 (wz P_bread_conv); C8 (wz P_b64_read); C8 (wz P_b64_puts); C8 (wz 0); C8 (wz P_b64_ctrl);
     C8 (wz P_b64_new); C8 (wz P_b64_free); C8 (wz P_b64_callback_ctrl)].

Definition BIOBUFMEM_SIZE : Z := 16.
Definition BIO_FLAGS_MEM_RDONLY : Z := 512.
Definition BIO_FLAGS_MEM_LEGACY_EOF : Z := 4096.  (* [comment removed for export] *)
Definition BIO_FLAGS_RETRY_MASK : Z := 15.        (* [comment removed for export] *)
Definition BIO_CTRL_EOF : Z := 2.  Definition BIO_CTRL_PUSH : Z := 6.

(* [comment removed for export] *)
Record membio := mkMB {
  mb_buf : Z; mb_len : Z; mb_pos : Z;
  mb_flags : Z; mb_numf : Z; mb_nread : Z; mb_next : Z; mb_prev : Z;
  mb_bb : Z; mb_bm : Z; mb_rp : Z;
  mb_id : bptr; mb_bbid : bptr; mb_bmid : bptr; mb_rpid : bptr }.
Definition membio_bio (R : membio) : biorep :=
  mkBIO A_mem_buf_method 1 1 (mb_flags R) 0 (mb_numf R) (mb_bb R) (mb_next R) (mb_prev R) 1 (mb_nread R) 0.
Definition MEMBIO (LB : list block) (m : mem) (a : Z) (R : membio) : Prop :=
     rw_cells asegs m a (bio_cells (membio_bio R))
  /\ rw_cells asegs m (mb_bb R) [C8 (wz (mb_bm R)); C8 (wz (mb_rp R))]
  /\ rw_cells asegs m (mb_bm R) (buf_cells (mkBUF (mb_len R - mb_pos R) (mb_buf R + mb_pos R) (mb_len R - mb_pos R) 0))
  /\ rw_cells asegs m (mb_rp R) (buf_cells (mkBUF (mb_len R) (mb_buf R) (mb_len R) 0))
  /\ In (mb_id R, a, BIO_SIZE) LB /\ In (mb_bbid R, mb_bb R, BIOBUFMEM_SIZE) LB
  /\ In (mb_bmid R, mb_bm R, BUFMEM_SIZE) LB /\ In (mb_rpid R, mb_rp R, BUFMEM_SIZE) LB
  /\ ablock_range HI a BIO_SIZE /\ ablock_range HI (mb_bb R) BIOBUFMEM_SIZE /\ ablock_range HI (mb_bm R) BUFMEM_SIZE /\ ablock_range HI (mb_rp R) BUFMEM_SIZE
  /\ 0 <= mb_pos R <= mb_len R /\ 0 <= mb_len R < 2^31 /\ 0 < mb_buf R /\ mb_buf R + mb_len R <= aceil
  /\ 0 <= mb_flags R < 2^31 /\ Z.land (mb_flags R) BIO_FLAGS_MEM_RDONLY = BIO_FLAGS_MEM_RDONLY /\ Z.land (mb_flags R) 128 = 0
  /\ mb_numf R = 0                                                             (* [comment removed for export] *)
  /\ 0 <= mb_nread R /\ mb_nread R + (mb_len R - mb_pos R) < 2^63       (* [comment removed for export] *)
  /\ 0 <= mb_next R < 2^64 /\ 0 <= mb_prev R < 2^64.
Definition blocks_MEMBIO (a : Z) (R : membio) : list block :=
  [(mb_id R, a, BIO_SIZE); (mb_bbid R, mb_bb R, BIOBUFMEM_SIZE); (mb_bmid R, mb_bm R, BUFMEM_SIZE); (mb_rpid R, mb_rp R, BUFMEM_SIZE)].
(* [comment removed for export] *)
Definition MEMBIO_foot (a : Z) (R : membio) : list (Z * Z) := [(a, a + BIO_SIZE); (mb_bm R, mb_bm R + BUFMEM_SIZE)].
(* [comment removed for export] *)
Definition MEMBIO_apart (a : Z) (R : membio) : Prop :=
     (a + BIO_SIZE <= mb_bb R \/ mb_bb R + BIOBUFMEM_SIZE <= a)
  /\ (a + BIO_SIZE <= mb_bm R \/ mb_bm R + BUFMEM_SIZE <= a)
  /\ (a + BIO_SIZE <= mb_rp R \/ mb_rp R + BUFMEM_SIZE <= a)
  /\ (mb_bb R + BIOBUFMEM_SIZE <= mb_bm R \/ mb_bm R + BUFMEM_SIZE <= mb_bb R)
  /\ (mb_bb R + BIOBUFMEM_SIZE <= mb_rp R \/ mb_rp R + BUFMEM_SIZE <= mb_bb R)
  /\ (mb_bm R + BUFMEM_SIZE <= mb_rp R \/ mb_rp R + BUFMEM_SIZE <= mb_bm R).
Definition MEMBIO_sep (a : Z) (R : membio) : Prop :=
     MEMBIO_apart a R
  /\ (mb_buf R + mb_len R <= a \/ a + BIO_SIZE <= mb_buf R)
  /\ (mb_buf R + mb_len R <= mb_bb R \/ mb_bb R + BIOBUFMEM_SIZE <= mb_buf R)
  /\ (mb_buf R + mb_len R <= mb_bm R \/ mb_bm R + BUFMEM_SIZE <= mb_buf R)
  /\ (mb_buf R + mb_len R <= mb_rp R \/ mb_rp R + BUFMEM_SIZE <= mb_buf R).
Definition MEMBIO_BYTES : Z := BIO_SIZE + BIOBUFMEM_SIZE + BUFMEM_SIZE + BUFMEM_SIZE.     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition mb_advance (R : membio) (n fl : Z) : membio :=
  mkMB (mb_buf R) (mb_len R) (mb_pos R + n) fl (mb_numf R) (mb_nread R + n) (mb_next R) (mb_prev R)
       (mb_bb R) (mb_bm R) (mb_rp R) (mb_id R) (mb_bbid R) (mb_bmid R) (mb_rpid R).
Definition mb_with_hdr (R : membio) (fl numf next prev : Z) : membio :=
  mkMB (mb_buf R) (mb_len R) (mb_pos R) fl numf (mb_nread R) next prev
       (mb_bb R) (mb_bm R) (mb_rp R) (mb_id R) (mb_bbid R) (mb_bmid R) (mb_rpid R).

(* [comment removed for export] *)
Definition B64CTX_SIZE : Z := 2584.
Definition O_B64_BASE64 : Z := 32.  Definition O_B64_ENCBUF : Z := 2568.
Definition BIO_FLAGS_BASE64_NO_NL : Z := 256.
Record b64frep := mkBF {
  bf_flags : Z; bf_retry : Z; bf_nread : Z; bf_next : Z; bf_prev : Z;
  bf_ctx : Z; bf_enc : Z; bf_id : bptr; bf_cid : bptr; bf_eid : bptr }.
Definition b64f_bio (R : b64frep) : biorep :=
  mkBIO A_b64_method 1 1 (bf_flags R) (bf_retry R) 0 (bf_ctx R) (bf_next R) (bf_prev R) 1 (bf_nread R) 0.
Definition b64ctx_fresh_cells (enc : Z) (junk : list byte) : list cell :=
  [C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 1); C4 (wz 1); C4 (wz 0);
   C8 (wz enc); CB 2528 junk; C8 (wz 0); C8 (wz 0)].
Definition b64ctx_used_cells (enc : Z) (hdr : list byte) (junk : list byte) (elen : Z) : list cell :=
  [CB 32 hdr; C8 (wz enc); CB 2528 junk; C8 (wz 0); C8 (wz elen)].
Definition B64F_blocks (LB : list block) (a : Z) (R : b64frep) : Prop :=
     In (bf_id R, a, BIO_SIZE) LB /\ In (bf_cid R, bf_ctx R, B64CTX_SIZE) LB /\ In (bf_eid R, bf_enc R, 92) LB
  /\ ablock_range HI a BIO_SIZE /\ ablock_range HI (bf_ctx R) B64CTX_SIZE /\ ablock_range HI (bf_enc R) 92
  /\ 0 <= bf_flags R < 2^31 /\ 0 <= bf_retry R < 2^32 /\ 0 <= bf_nread R < 2^63 /\ 0 <= bf_next R < 2^64 /\ 0 <= bf_prev R < 2^64.
Definition B64F_fresh (LB : list block) (m : mem) (a : Z) (R : b64frep) : Prop :=
     rw_cells asegs m a (bio_cells (b64f_bio R))
  /\ (exists junk, length junk = 2528%nat /\ rw_cells asegs m (bf_ctx R) (b64ctx_fresh_cells (bf_enc R) junk))
  /\ B64F_blocks LB a R /\ Z.land (bf_flags R) BIO_FLAGS_BASE64_NO_NL = BIO_FLAGS_BASE64_NO_NL /\ bf_retry R = 0 /\ bf_nread R = 0.
Definition B64F_used (LB : list block) (m : mem) (a : Z) (R : b64frep) : Prop :=
     rw_cells asegs m a (bio_cells (b64f_bio R))
  /\ (exists hdr junk elen, length hdr = 32%nat /\ length junk = 2528%nat /\ 0 <= elen < 2^64
        /\ rw_cells asegs m (bf_ctx R) (b64ctx_used_cells (bf_enc R) hdr junk elen))
  /\ B64F_blocks LB a R.
(* [comment removed for export] *)
Definition B64F_apart (a : Z) (R : b64frep) : Prop :=
     (a + BIO_SIZE <= bf_ctx R \/ bf_ctx R + B64CTX_SIZE <= a)
  /\ (a + BIO_SIZE <= bf_enc R \/ bf_enc R + 92 <= a)
  /\ (bf_ctx R + B64CTX_SIZE <= bf_enc R \/ bf_enc R + 92 <= bf_ctx R).
Definition blocks_B64F (a : Z) (R : b64frep) : list block :=
  [(bf_id R, a, BIO_SIZE); (bf_cid R, bf_ctx R, B64CTX_SIZE); (bf_eid R, bf_enc R, 92)].
Definition B64F_foot (a : Z) (R : b64frep) : list (Z * Z) :=
  [(a, a + BIO_SIZE); (bf_ctx R, bf_ctx R + B64CTX_SIZE); (bf_enc R, bf_enc R + 92)].
Definition B64F_BYTES : Z := BIO_SIZE + B64CTX_SIZE + 92.
Definition bf_with_hdr (R : b64frep) (fl rt nr nx pv : Z) : b64frep :=
  mkBF fl rt nr nx pv (bf_ctx R) (bf_enc R) (bf_id R) (bf_cid R) (bf_eid R).

(* [comment removed for export] *)
(* [comment removed for export] *)
Record extrep := mkEXT { ex_type : Z; ex_len : Z; ex_val : Z; ex_val_o : oblk; ex_id : bptr }.
Definition EXT_SIZE : Z := 16.
Definition ext_cells (E : extrep) (pad : list byte) : list cell :=
  [C2 (wz (ex_type E)); C2 (wz (ex_len E)); CB 4 pad; C8 (wz (ex_val E))].
Definition EXTobj (LB : list block) (m : mem) (a : Z) (E : extrep) : Prop :=
  (exists pad, length pad = 4%nat /\ rw_cells asegs m a (ext_cells E pad))
  /\ In (ex_id E, a, EXT_SIZE) LB /\ ofield LB (ex_val E) (ex_val_o E).
Definition blocks_EXT (a : Z) (E : extrep) : list block := (ex_id E, a, EXT_SIZE) :: blocks_of (ex_val E) (ex_val_o E).

(* [comment removed for export] *)
Definition EXTS (LB : list block) (m : mem) (P : Z) (xs : option (skrep * list extrep)) : Prop :=
  match xs with
  | None => P = 0
  | Some (K, es) => 0 < P /\ SKobj LB m P K /\ length es = length (sk_elems K)
                  /\ Forall2 (fun p E => EXTobj LB m p E) (sk_elems K) es
  end.
Definition blocks_EXTS (P : Z) (xs : option (skrep * list extrep)) : list block :=
  match xs with
  | None => []
  | Some (K, es) => blocks_SK P K ++ concat (map (fun pe => blocks_EXT (fst pe) (snd pe)) (combine (sk_elems K) es))
  end.

Record entrep := mkENT {
  en_version : Z; en_pname : Z; en_pname_o : oblk; en_publen : Z; en_pub : Z; en_pub_o : oblk;
  en_nsuites : Z; en_suites : Z; en_suites_o : oblk; en_maxname : Z; en_cfgid : Z;
  en_exts : Z; en_exts_o : option (skrep * list extrep); en_loadtime : Z;
  en_forretry : Z; en_enclen : Z; en_encoded : Z; en_encoded_o : oblk; en_id : bptr }.
Definition ENTRY_SIZE : Z := 104.
Definition O_EN_PNAME : Z := 8.   Definition O_EN_PUBLEN : Z := 16.  Definition O_EN_PUB : Z := 24.
Definition O_EN_NSUITES : Z := 32. Definition O_EN_SUITES : Z := 40. Definition O_EN_MAXNAME : Z := 48.
Definition O_EN_EXTS : Z := 56.   Definition O_EN_LOADTIME : Z := 64. Definition O_EN_KEYSHARE : Z := 72.
Definition O_EN_FORRETRY : Z := 80. Definition O_EN_ENCLEN : Z := 88. Definition O_EN_ENCODED : Z := 96.
Definition entry_cells (E : entrep) (pad1 pad2 pad3 pad4 : list byte) : list cell :=
  [C2 (wz (en_version E)); CB 6 pad1; C8 (wz (en_pname E)); C8 (wz (en_publen E)); C8 (wz (en_pub E));
   C4 (wz (en_nsuites E)); CB 4 pad2; C8 (wz (en_suites E)); C1 (b8 (en_maxname E)); C1 (b8 (en_cfgid E)); CB 6 pad3;
   C8 (wz (en_exts E)); C8 (wz (en_loadtime E)); C8 (wz 0); C4 (wz (en_forretry E)); CB 4 pad4;
   C8 (wz (en_enclen E)); C8 (wz (en_encoded E))].
Definition ENTRYobj (LB : list block) (m : mem) (a : Z) (E : entrep) : Prop :=
  (exists pad1 pad2 pad3 pad4, length pad1 = 6%nat /\ length pad2 = 4%nat /\ length pad3 = 6%nat /\ length pad4 = 4%nat
      /\ rw_cells asegs m a (entry_cells E pad1 pad2 pad3 pad4))
  /\ In (en_id E, a, ENTRY_SIZE) LB
  /\ ofield LB (en_pname E) (en_pname_o E) /\ ofield LB (en_pub E) (en_pub_o E)
  /\ ofield LB (en_suites E) (en_suites_o E) /\ ofield LB (en_encoded E) (en_encoded_o E)
  /\ EXTS LB m (en_exts E) (en_exts_o E).
Definition blocks_ENTRY (a : Z) (E : entrep) : list block :=
  (en_id E, a, ENTRY_SIZE) :: blocks_of (en_pname E) (en_pname_o E) ++ blocks_of (en_pub E) (en_pub_o E)
  ++ blocks_of (en_suites E) (en_suites_o E) ++ blocks_of (en_encoded E) (en_encoded_o E)
  ++ blocks_EXTS (en_exts E) (en_exts_o E).

Record storerep := mkSTORE { es_entries : Z; es_entries_o : option (skrep * list entrep); es_id : bptr }.
Definition STORE_SIZE : Z := 24.
Definition ENTRIES (LB : list block) (m : mem) (P : Z) (xs : option (skrep * list entrep)) : Prop :=
  match xs with
  | None => P = 0
  | Some (K, es) => 0 < P /\ SKobj LB m P K /\ length es = length (sk_elems K)
                  /\ Forall2 (fun p E => ENTRYobj LB m p E) (sk_elems K) es
  end.
Definition STOREobj (LB : list block) (m : mem) (a : Z) (S : storerep) : Prop :=
  rw_cells asegs m a [C8 (wz (es_entries S)); C8 (wz 0); C8 (wz 0)]
  /\ In (es_id S, a, STORE_SIZE) LB /\ ENTRIES LB m (es_entries S) (es_entries_o S).
Definition blocks_STORE (a : Z) (S : storerep) : list block :=
  (es_id S, a, STORE_SIZE) ::
  match es_entries_o S with
  | None => []
  | Some (K, es) => blocks_SK (es_entries S) K ++ concat (map (fun pe => blocks_ENTRY (fst pe) (snd pe)) (combine (sk_elems K) es))
  end.
Definition store_empty (id : bptr) : storerep := mkSTORE 0 None id.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record errslot := mkSLOT { sl_flags : Z; sl_buffer : Z; sl_file : Z; sl_file_o : oblk; sl_line : Z; sl_func : Z; sl_func_o : oblk }.
Record errst := mkERRST { es_slots : list errslot; es_top : Z; es_bottom : Z }.
Definition ERRST_SIZE : Z := 904.
Definition O_ES_MARKS : Z := 64.   Definition O_ES_BUFFER : Z := 128. Definition O_ES_DATA : Z := 256.
Definition O_ES_DSIZE : Z := 384.  Definition O_ES_DFLAGS : Z := 512. Definition O_ES_FILE : Z := 576.
Definition O_ES_LINE : Z := 704.   Definition O_ES_FUNC : Z := 768.   Definition O_ES_TOP : Z := 896.
Definition zero16 : list word := repeat (wz 0) 16.
Definition ERRST (LB : list block) (m : mem) (a : Z) (E : errst) : Prop :=
  length (es_slots E) = 16%nat /\ 0 <= es_top E < 16 /\ 0 <= es_bottom E < 16
  /\ u32arr asegs m a (map (fun s => wz (sl_flags s)) (es_slots E))
  /\ u32arr asegs m (a + O_ES_MARKS) zero16
  /\ u64arr asegs m (a + O_ES_BUFFER) (map (fun s => wz (sl_buffer s)) (es_slots E))
  /\ u64arr asegs m (a + O_ES_DATA) zero16
  /\ u64arr asegs m (a + O_ES_DSIZE) zero16
  /\ u32arr asegs m (a + O_ES_DFLAGS) zero16
  /\ u64arr asegs m (a + O_ES_FILE) (map (fun s => wz (sl_file s)) (es_slots E))
  /\ u32arr asegs m (a + O_ES_LINE) (map (fun s => wz (sl_line s)) (es_slots E))
  /\ u64arr asegs m (a + O_ES_FUNC) (map (fun s => wz (sl_func s)) (es_slots E))
  /\ rw_cells asegs m (a + O_ES_TOP) [C4 (wz (es_top E)); C4 (wz (es_bottom E))]
  /\ Forall (fun s => ofield LB (sl_file s) (sl_file_o s) /\ ofield LB (sl_func s) (sl_func_o s)
                      /\ 0 <= sl_flags s < 2^32 /\ 0 <= sl_buffer s < 2^64 /\ 0 <= sl_line s < 2^32) (es_slots E).
Definition blocks_slot (s : errslot) : list block := blocks_of (sl_file s) (sl_file_o s) ++ blocks_of (sl_func s) (sl_func_o s).
Definition blocks_ERRST (E : errst) : list block := concat (map blocks_slot (es_slots E)).
(* [comment removed for export] *)
Definition slot_clear (line : Z) : errslot := mkSLOT 0 0 0 None line 0 None.
Definition errst_zero : errst := mkERRST (repeat (slot_clear 0) 16) 0 0.
Definition errst_cleared : errst := mkERRST (repeat (slot_clear (2^32 - 1)) 16) 0 0.
Definition errst_canonical (E : errst) : Prop := E = errst_zero \/ E = errst_cleared.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition VPM_SIZE : Z := 136.
Definition O_VPM_HOSTS : Z := 56.
Definition XBUF_SIZE : Z := 16.      (* [comment removed for export] *)
(* [comment removed for export] *)
Record xbufrep := mkXB { xb_data : Z; xb_len : Z; xb_id : bptr; xb_did : bptr }.
Definition XBUFobj (LB : list block) (m : mem) (a : Z) (X : xbufrep) : Prop :=
  rw_cells asegs m a [C8 (wz (xb_data X)); C8 (wz (xb_len X))]
  /\ In (xb_id X, a, XBUF_SIZE) LB /\ 0 < xb_data X /\ 0 <= xb_len X /\ In (xb_did X, xb_data X, xb_len X + 1) LB.
Definition blocks_XBUF (a : Z) (X : xbufrep) : list block := [(xb_id X, a, XBUF_SIZE); (xb_did X, xb_data X, xb_len X + 1)].
(* [comment removed for export] *)
Definition HOSTS (LB : list block) (m : mem) (P : Z) (xs : option (skrep * list xbufrep)) : Prop :=
  match xs with
  | None => P = 0
  | Some (K, bs) => 0 < P /\ SKobj LB m P K /\ length bs = length (sk_elems K)
                  /\ Forall2 (fun p X => XBUFobj LB m p X) (sk_elems K) bs
  end.
Definition blocks_HOSTS (P : Z) (xs : option (skrep * list xbufrep)) : list block :=
  match xs with
  | None => []
  | Some (K, bs) => blocks_SK P K ++ concat (map (fun px => blocks_XBUF (fst px) (snd px)) (combine (sk_elems K) bs))
  end.
Record vpmrep := mkVPM { vp_hosts : Z; vp_hosts_o : option (skrep * list xbufrep); vp_id : bptr }.
(* [comment removed for export] *)
Definition vpm_cells (V : vpmrep) : list cell :=
  [CB 36 (zeros 36); C4 (wz 0); C8 (wz (2^64 - 1)); C8 (wz 0); C8 (wz (vp_hosts V)); C8 (wz 0); C8 (wz 0);
   C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)].
Definition VPMobj (LB : list block) (m : mem) (a : Z) (V : vpmrep) : Prop :=
  rw_cells asegs m a (vpm_cells V) /\ In (vp_id V, a, VPM_SIZE) LB /\ HOSTS LB m (vp_hosts V) (vp_hosts_o V).
Definition blocks_VPM (a : Z) (V : vpmrep) : list block := (vp_id V, a, VPM_SIZE) :: blocks_HOSTS (vp_hosts V) (vp_hosts_o V).
Definition vpm_empty (id : bptr) : vpmrep := mkVPM 0 None id.

(* [comment removed for export] *)
Definition is_alnumZ (c : Z) : bool := ((48 <=? c) && (c <=? 57)) || ((65 <=? c) && (c <=? 90)) || ((97 <=? c) && (c <=? 122)).
Definition label_charZ (c : Z) : bool := is_alnumZ c || (c =? 95).
Fixpoint hn_loop (cs : list Z) (i part prev : Z) : bool :=
  match cs with
  | [] => negb ((prev =? 46) || (prev =? 45))
  | c :: cs' =>
      if c =? 46 then
        if ((part =? 0) && negb (i =? 0)) || (prev =? 45) then false else hn_loop cs' (i + 1) 0 c
      else if (part =? 0) && (c =? 45) then false
      else if negb (label_charZ c || (c =? 45)) then false
      else if 63 <? part + 1 then false
      else hn_loop cs' (i + 1) (part + 1) c
  end.
Definition hostname_ok (bs : list byte) : bool :=
  (2 <=? zlength bs) && (zlength bs <=? 256) && hn_loop (map bv_unsigned bs) 0 0 0.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition MUTEX_SIZE : Z := 40.
Definition MUTEX (m : mem) (a : Z) (lk : Z) : Prop :=
  rw_cells asegs m a [CB 4 [b8 0; b8 0; b8 0; b8 0]; C4 (wz lk); C4 (wz 0)].
Definition mutex_foot (a : Z) : list (Z * Z) := [(a + 4, a + 8)].
Definition MUTEX_HELD : Z := 16.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma zlength_nil : forall A, @zlength A [] = 0. Proof. reflexivity. Qed.
Lemma zlength_cons : forall A (x : A) l, zlength (x :: l) = zlength l + 1.
Proof. intros. unfold zlength. cbn [length]. lia. Qed.
Lemma zlength_app : forall A (l1 l2 : list A), zlength (l1 ++ l2) = zlength l1 + zlength l2.
Proof. intros. unfold zlength. rewrite length_app. lia. Qed.

End HCW.
