(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the auxv facts are stated at the revision's auxv layout (pair k's key and value at bytes 16k and 16k + 8 from the auxv pointer, one fact per word), and also give, for one of the two CONFIG_RSEQ values, the key of every pair up to and including AT_NULL and the span the unwinder's auxv walk reads, as readable. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Mem Frame Cells Step Arr ImageA RzCPS.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.B Require Import Layout RT_iface D_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation mem := (word -> option byte).

Definition EL_AUXV_CELL : Z := 0x6d7140.

Definition EL_XDATA1 : Z := 0x17d590.
Definition EL_XDATA2 : Z := 0x17d968.
Definition el_xdataA (m : mem) : Prop :=
  rw_cells bsegs m 0x17d590 [C8 (Z_to_bv 64 0x1765d8); C8 (Z_to_bv 64 0x115a58)]
  /\ rw_cells bsegs m 0x17d968 [C8 (Z_to_bv 64 0xf8858); C8 (Z_to_bv 64 0xf8964)].
Lemma el_xdata_agree : forall m m' : mem, el_xdataA m ->
  agree_on (fun x => 0x17d590 <= x < 0x17d590 + 16 \/ 0x17d968 <= x < 0x17d968 + 16) m m' -> el_xdataA m'.
Proof.
  intros m m' [X1 X2] AG. split.
  - apply (rw_cells_agree_nw bsegs m m' _ _ X1). intros a Ha. apply AG. cbn [cells_size csize Nat.add] in Ha. left. lia.
  - apply (rw_cells_agree_nw bsegs m m' _ _ X2). intros a Ha. apply AG. cbn [cells_size csize Nat.add] in Ha. right. lia.
Qed.
Definition EL_AT_PHDR : Z := 0x10040.

(* Auxv retabled to the revision's vector (75d69e00:theories/LinuxProcessSem/
   StackLayout.v:229-266): pair k's KEY is at byte 16*k off the auxv pointer and
   its VALUE at 16*k + 8.  The old spec was the ten COMPACTED pairs of the
   pre-revision vector laid out contiguously from av, AT_PHDR first:
     AT_HWCAP  48/56   -> 160/168     AT_UID    80/88   -> 304/312
     AT_PAGESZ 64/72   -> 176/184     AT_EUID   96/104  -> 320/328
     AT_PHDR    0/8    -> 208/216     AT_SECURE 112/120 -> 368/376
     AT_PHENT  16/24   -> 224/232     AT_RANDOM 128/136 -> 384/392
     AT_PHNUM  32/40   -> 240/248
   The payloads are unchanged; only the indices moved.  The claim is one fact per
   WORD rather than one contiguous run, because the revision's pairs 0..9, 12,
   16..18, 21, 22 and 25 sit between the ones named here and nothing in this unit
   knows their values.  The old AT_NULL words (144/152) are not carried over:
   AT_NULL is pair 26 + 2*r with r the kernel's rseq flag, so a literal index
   would pin that flag.  Span 160 -> 400. *)
Definition el_auxv_word (m : mem) (a v : Z) : Prop := bytes_at bsegs m a (le8 (Z_to_bv 64 v)).

Definition el_auxv_at (m : mem) (av x16 x11 rnd : Z) : Prop :=
  el_auxv_word m (av + 160) 16 /\ el_auxv_word m (av + 168) x16
  /\ el_auxv_word m (av + 176) 6 /\ el_auxv_word m (av + 184) 4096
  /\ el_auxv_word m (av + 208) 3 /\ el_auxv_word m (av + 216) EL_AT_PHDR
  /\ el_auxv_word m (av + 224) 4 /\ el_auxv_word m (av + 232) 56
  /\ el_auxv_word m (av + 240) 5 /\ el_auxv_word m (av + 248) 11
  /\ el_auxv_word m (av + 304) 11 /\ el_auxv_word m (av + 312) x11
  /\ el_auxv_word m (av + 320) 12 /\ el_auxv_word m (av + 328) x11
  /\ el_auxv_word m (av + 368) 23 /\ el_auxv_word m (av + 376) 0
  /\ el_auxv_word m (av + 384) 25 /\ el_auxv_word m (av + 392) rnd.

(* LPS 727298f3: the unwinder walks the whole auxv.  musl's [static_dl_iterate_phdr], on
   the __cxa_throw path, runs [for (i=0; libc.auxv[i]; i+=2) if (libc.auxv[i] < AUX_CNT)
   aux[libc.auxv[i]] = libc.auxv[i+1]] before it reads AT_PHDR, AT_PHENT and AT_PHNUM, so
   its symbolic runs need the key of every pair up to and including AT_NULL, and every
   word it loads readable.  [el_auxv_keys b] lists (byte offset of pair k's key, key) for
   the keys [el_auxv_at] does not name, for the CONFIG_RSEQ value [b]: AT_SYSINFO_EHDR,
   the eight cache words, AT_MINSIGSTKSZ, AT_CLKTCK, AT_BASE, AT_FLAGS, AT_ENTRY,
   AT_GID, AT_EGID, AT_EXECFN, then the two AT_RSEQ pairs when the kernel has rseq, then
   AT_NULL (pair 26 + 2 b).  [el_auxv_span b] is the readable span from pair 0 to
   AT_NULL's key (16 * (26 + 2 b) + 8 bytes).  The keys are the ones every hand-off
   state AS/AsanStartupCert.v and AS/BothStartupCert.v compute holds at the auxv base,
   at both flags, with a [KUnk] over the whole vector (B/HandoffAux.v [hs_auxv_ok]
   checks them on each). *)
Definition el_auxv_keys (b : bool) : list (Z * Z) :=
  [(0, 33); (16, 40); (32, 41); (48, 42); (64, 43); (80, 44); (96, 45); (112, 46); (128, 47); (144, 51);
   (192, 17); (256, 7); (272, 8); (288, 9); (336, 13); (352, 14); (400, 31)]
  ++ (if b then [(416, 27); (432, 28); (448, 0)] else [(416, 0)]).
Definition el_auxv_span (b : bool) : Z := if b then 456 else 424.
Definition el_auxv_walk (m : mem) (av : Z) : Prop :=
  exists b : bool,
    Forall (fun p => el_auxv_word m (av + fst p) (snd p)) (el_auxv_keys b)
    /\ (forall i, 0 <= i < el_auxv_span b -> m (wa (av + i)) <> None)
    /\ 0 <= av /\ av + 456 <= USTACK_TOP.

Definition el_auxvA (lo : Z) (m : mem) : Prop :=
  exists av x16 x11 rnd,
    ro_cells bsegs m EL_AUXV_CELL [C8 (Z_to_bv 64 av)]
    /\ el_auxv_at m av x16 x11 rnd
    /\ lo <= av /\ av + 400 <= USTACK_TOP /\ av mod 8 = 0 /\ 0 <= x16 < 2^64 /\ 0 <= x11 < 2^64 /\ 0 <= rnd < 2^64
    /\ el_auxv_walk m av.

Definition auxc (x : Z) : Prop := EL_AUXV_CELL <= x < EL_AUXV_CELL + 8.

Lemma el_auxv_weaken : forall lo lo' m, el_auxvA lo m -> lo' <= lo -> el_auxvA lo' m.
Proof.
  intros lo lo' m (av & x16 & x11 & rnd & C & B & H1 & H2 & H3 & H4 & H5 & H6 & HW) Hle. exists av, x16, x11, rnd.
  split; [exact C|]. split; [exact B|]. do 6 (split; [lia|]). exact HW.
Qed.

Lemma el_auxv_walk_agree : forall lo av m m', lo <= av -> el_auxv_walk m av ->
  agree_on (fun x => lo <= x < USTACK_TOP) m m' -> el_auxv_walk m' av.
Proof.
  intros lo av m m' Hlo (b & HK & HR & H0 & HT) AGS. exists b. split; [| split; [| exact (conj H0 HT)]].
  - rewrite Forall_forall in HK |- *. intros p Hp.
    assert (PB : 0 <= fst p <= 448).
    { destruct b; cbn [el_auxv_keys app In] in Hp; repeat (destruct Hp as [<-|Hp]; [cbn [fst]; lia|]); destruct Hp. }
    apply (bytes_at_agree bsegs m m' _ _ (HK p Hp)). intros x Hx. apply AGS. cbv beta.
    first [rewrite length_le8 in Hx | rewrite Mem.length_le8 in Hx | rewrite length_N_to_le_bytes in Hx]. unfold USTACK_TOP in *. lia.
  - intros i Hi. assert (SP : el_auxv_span b <= 456) by (destruct b; cbn [el_auxv_span]; lia).
    rewrite (AGS (wa (av + i))); [exact (HR i Hi)|].
    cbv beta. rewrite wa_unsigned by (unfold USTACK_TOP in *; lia). unfold USTACK_TOP in *. lia.
Qed.

Lemma el_auxv_agree : forall lo m m', el_auxvA lo m ->
  agree_on auxc m m' -> agree_on (fun x => lo <= x < USTACK_TOP) m m' -> el_auxvA lo m'.
Proof.
  intros lo m m' (av & x16 & x11 & rnd & C & B & Hlo & Hhi & H3 & H4 & H5 & H6 & HW) AGC AGS. exists av, x16, x11, rnd.
  split; [| split; [| split; [exact Hlo| split; [exact Hhi| split; [exact H3| split; [exact H4| split; [exact H5| split; [exact H6|]]]]]]]].
  - apply (ro_cells_agree bsegs m m' _ _ C). intros x Hx. apply AGC. unfold auxc. cbn [cells_size csize Nat.add] in Hx. lia.
  - assert (AW : forall a v, lo <= a -> a + 8 <= USTACK_TOP -> el_auxv_word m a v -> el_auxv_word m' a v).
    { intros a v Ha Hb Hv. apply (bytes_at_agree bsegs m m' _ _ Hv). intros x Hx. apply AGS. cbv beta.
      first [rewrite length_le8 in Hx | rewrite Mem.length_le8 in Hx | rewrite length_N_to_le_bytes in Hx]. lia. }
    unfold el_auxv_at in B |- *.
    destruct B as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15 & B16 & B17 & B18).
    (* Exactly 17 splits, not [repeat apply conj]: [el_auxv_word] unfolds to [bytes_at],
       which is itself a conjunction, so [repeat] would split the words apart too. *)
    do 17 (apply conj; [apply AW; [lia| lia| assumption]|]). apply AW; [lia| lia| assumption].
  - exact (el_auxv_walk_agree lo av m m' Hlo HW AGS).
Qed.

Lemma auxc_client_static : forall x, auxc x -> client_static x.
Proof.
  intros x Hx. unfold auxc, EL_AUXV_CELL in Hx. split.
  - exists 0x6b52d0, 0x6d8898. split; [unfold CLIENT_STATIC; cbn; tauto| lia].
  - intros (lo & hi & Hin & Hlh). unfold RT_STATIC in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
Qed.

Lemma auxc_of_pres : forall live frames sp m m', rt_pres live frames sp m m' -> agree_on auxc m m'.
Proof. intros live frames sp m m' P x Hx. apply P. right; left. exact (auxc_client_static _ Hx). Qed.

Lemma auxc_of_pres_ex : forall live frames sp d n m m', rt_pres_ex live frames sp d n m m' ->
  (d + n <= EL_AUXV_CELL \/ EL_AUXV_CELL + 8 <= d) -> agree_on auxc m m'.
Proof.
  intros live frames sp d n m m' P Hd x Hx. apply P; [right; left; exact (auxc_client_static _ Hx)|]. unfold auxc in Hx. lia.
Qed.

Lemma auxc_of_pres_fp : forall live frames sp W m m', rt_pres_fp live frames sp W m m' ->
  (forall x, auxc x -> outside W x) -> agree_on auxc m m'.
Proof. intros live frames sp W m m' P HW x Hx. apply P; [right; left; exact (auxc_client_static _ Hx)| exact (HW _ Hx)]. Qed.

Lemma auxc_of_munch : forall W m m', munch W m m' -> (forall x, auxc x -> outside W x) -> agree_on auxc m m'.
Proof. intros W m m' MU HW x Hx. apply MU. exact (HW _ Hx). Qed.

Lemma agree_on_auxc_trans : forall m1 m2 m3, agree_on auxc m1 m2 -> agree_on auxc m2 m3 -> agree_on auxc m1 m3.
Proof. intros m1 m2 m3 A B x Hx. rewrite (B x Hx). exact (A x Hx). Qed.

Lemma el_auxv_munch : forall lo W m m', el_auxvA lo m -> munch W m m' ->
  (forall x, auxc x \/ lo <= x < USTACK_TOP -> outside W x) -> el_auxvA lo m'.
Proof.
  intros lo W m m' H MU HW. apply (el_auxv_agree lo m m' H).
  - apply (auxc_of_munch W m m' MU). intros x Hx. apply HW. left. exact Hx.
  - intros a Ha. apply MU. apply HW. right. exact Ha.
Qed.

Lemma el_auxv_pres : forall lo live frames sp m m', el_auxvA lo m -> rt_pres live frames sp m m' -> sp <= lo -> el_auxvA lo m'.
Proof.
  intros lo live frames sp m m' H P Hsp. apply (el_auxv_agree lo m m' H (auxc_of_pres _ _ _ _ _ P)).
  intros a Ha. apply P. left. cbv beta in Ha. lia.
Qed.

Lemma el_auxv_pres_ex : forall lo live frames sp d n m m', el_auxvA lo m -> rt_pres_ex live frames sp d n m m' -> sp <= lo ->
  (d + n <= EL_AUXV_CELL \/ EL_AUXV_CELL + 8 <= d) -> d + n <= lo -> el_auxvA lo m'.
Proof.
  intros lo live frames sp d n m m' H P Hsp Hd Hdl. apply (el_auxv_agree lo m m' H (auxc_of_pres_ex _ _ _ _ _ _ _ P Hd)).
  intros a Ha. cbv beta in Ha. apply P; [left; lia| lia].
Qed.

Lemma el_auxv_pres_fp : forall lo live frames sp W m m', el_auxvA lo m -> rt_pres_fp live frames sp W m m' -> sp <= lo ->
  (forall x, auxc x \/ lo <= x < USTACK_TOP -> outside W x) -> el_auxvA lo m'.
Proof.
  intros lo live frames sp W m m' H P Hsp HW. apply (el_auxv_agree lo m m' H).
  - apply (auxc_of_pres_fp _ _ _ _ _ _ P). intros x Hx. apply HW. left. exact Hx.
  - intros a Ha. cbv beta in Ha. apply P; [left; lia| apply HW; right; exact Ha].
Qed.

Lemma auxc_range : forall x, auxc x -> 0x6d7140 <= x < 0x6d7148.
Proof. intros x Hx. unfold auxc, EL_AUXV_CELL in Hx. lia. Qed.

Lemma bytes_at_u64s : forall (m : mem) a ws,
  0 <= a -> a + 8 * Z.of_nat (length ws) <= 2 ^ 64 ->
  (forall j w, nth_error ws j = Some w -> bytes_at bsegs m (a + 8 * Z.of_nat j) (le8 w)) -> bytes_at bsegs m a (u64s ws).
Proof.
  intros m a ws. revert a. induction ws as [|w ws IH]; intros a Ha Hl H.
  - apply bytes_at_nil. cbn [length Z.of_nat] in Hl. lia.
  - cbn [u64s]. apply (proj2 (bytes_at_app _ _ _ _ _)). split.
    + pose proof (H 0%nat w eq_refl) as X. rewrite Z.mul_0_r, Z.add_0_r in X. exact X.
    + rewrite length_le8. change (Z.of_nat 8) with 8. apply IH; [lia| cbn [length] in Hl; lia|].
      intros j w' Hn. pose proof (H (S j) w' Hn) as X. replace (a + 8 * Z.of_nat (S j)) with (a + 8 + 8 * Z.of_nat j) in X by lia. exact X.
Qed.
