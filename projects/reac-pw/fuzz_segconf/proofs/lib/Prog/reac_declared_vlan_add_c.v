From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
From Stdlib Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

(** reac_declared_vlan_add(tab, max, n, parent, vid) (reac_declared_vlan.c:65-80; at 0x15c50 in the image
    3776ca44d75c; 276 bytes, frame 80 bytes, saves ra and s0-s8).
    As compiled: -1 when tab, n or parent is 0 (three `beqz`; the premise excludes them); s7 = *n (`lw`, read once
    for the search); the search (0x15cb0 .. `bnez s8` 0x15cd0, s6 = &tab[i], s8 = *n - i)
    compares `lhu 0x10(s6)` with vid (the whole register: a uint16_t argument arrives zero-extended) and, when they
    are equal, calls strcmp(tab[i].parent, parent) (`jal` 0x15cc0); the first 0 returns 0; then *n >= max (`bge s7,
    s5`, signed) returns -1; else memset(tab + 18 *n, 0, 18) (`jal` 0x15cec), strncpy(tab[*n].parent, parent, 15)
    (`jal` 0x15d04; *n is reloaded after each call), tab[*n].vid = vid (`sh` 0x15d14), *n = *n + 1 (`sw` 0x15d20),
    and it returns 1.
    It reads *n, the entries tab[0 .. *n) and the string at parent with its slack (strncpy reads words). It writes its
    frame and strncpy's, [sp - ADD_STACK, sp), and, when it appends, the entry tab[*n] (18 bytes) and *n: never past
    that entry, so never the guard entry tab[max] (the spine's
    vlans_are states the guard only as length tab <= cap; lemmas vtab_W_spares_guard, add_W_spares_guard,
    add_guard_kept).

    Post in the spine's terms: a0 and the table are SegModel.vlan_add t max p vid (1 appended, 0 duplicate, -1 full;
    -1 is the word 2^64 - 1, ret_post's Z_to_bv 64): the table holds snd (vlan_add t max p vid) (seg_spec.rtab_at)
    and *n its length. The appended entry is the memset's zeros with the 15-byte strncpy over them and the vid:
    firstn 15 p, its NUL, zeros, le2 vid (seg_spec.rvlan_enc).

    Callee contracts its walk takes as premises:
    - strcmp_contract (Prog/strcmp_c.v, STRCMP = 0x1ebf8; commit 06702a5f1f22): both
      strings NUL-terminated (tab[i].parent by rvlan_enc's cstr_enc 16), no stack, no store; r = 0 <-> equal is
      SegModel.strcmp = 0 on C strings (Spec/SegBridge.v's bridge_strcmp);
    - memset_contract (Prog/memset_c.v, MEMSET = 0x1e930): the 18 bytes of tab[*n] present and writable (vtab_pre's
      free entries);
    - strncpy_contract (Prog/strncpy_c.v, STRNCPY = 0x1ede4; commit 811f45dd6ed2):
      the 15 destination bytes, the source with its slack apart from them and from strncpy's 32 bytes of stack.
    ADD_STACK = 80 + 32 (strncpy's; strcmp and memset use none).

    Call site: reac_segconf_declared 0x15a3c (reac_segconf.c:574) with a0 = tab, a1 = max, a2 = n as declared
    received them (the table and *n as its loop keeps them: rtab_at of the current table, length <= max, the rest of
    the block free and writable), a3 = parent = declared's sp + 0x10 (the C string split left there; its slack is the
    rest of the 16-byte buffer), a4 = vid (`lhu`: below 2^16, zero-extended). *)
Definition REAC_DECLARED_VLAN_ADD : Z := 0x15c50.
Definition ADD_STACK : Z := 80 + 32.

(** The table and count cell add and reac_segconf_declared receive: tab a nonzero 16-aligned block of max + 1 entries
    (calloc(cap + 1, 18)) whose first length t entries hold t (rtab_at) and whose next max - length t entries are
    present and writable, length t <= max < 2^31; *n = length t in a nonzero 4-aligned writable int cell outside the
    block; block and cell apart from the stack region [lo, sp). The guard entry tab[max] is neither read nor written.
    *)
Definition vtab_pre (m : word -> option byte) (sp lo tab max n : Z) (t : list (list Z * Z)) : Prop :=
  tab <> 0 /\ tab mod 16 = 0 /\ rtab_at rsegs m tab t /\ Z.of_nat (length t) <= max < 2 ^ 31 /\
  (exists free, rw_cells rsegs m (tab + RVLAN_SIZE * Z.of_nat (length t))
                  [CB (Z.to_nat (RVLAN_SIZE * (max - Z.of_nat (length t)))) free]) /\
  apart tab (RVLAN_SIZE * (max + 1)) lo sp /\
  n <> 0 /\ n mod 4 = 0 /\ rw_cells rsegs m n [C4 (Z_to_bv 64 (Z.of_nat (length t)))] /\
  apart n 4 lo sp /\ apart n 4 tab (tab + RVLAN_SIZE * (max + 1)).

(** parent the C string p with its slack (strncpy reads words): its string, NUL and 7 bytes apart from the stack and
    from the table block; vid the uint16_t. *)
Definition add_pre (m : word -> option byte) (sp lo tab max n parent vid : Z) (t : list (list Z * Z)) (p : list Z)
    : Prop :=
  vtab_pre m sp lo tab max n t /\
  parent <> 0 /\ cstr_at rsegs m parent p /\ apart parent (Z.of_nat (length p) + 8) lo sp /\
  apart parent (Z.of_nat (length p) + 8) tab (tab + RVLAN_SIZE * (max + 1)) /\
  0 <= vid < 65536 /\
  stack_ok rsegs m lo sp ADD_STACK /\ mem_inv rsegs m.

(** The bytes add and reac_segconf_declared write: the frames [sp - depth, sp), the entries appended to a table of
    length t that now has length t', and *n when the table grew. *)
Definition vtab_W (depth sp tab n : Z) (t t' : list (list Z * Z)) : list ivl :=
  [(sp - depth, sp); (tab + RVLAN_SIZE * Z.of_nat (length t), tab + RVLAN_SIZE * Z.of_nat (length t'))] ++
  (if (length t <? length t')%nat then [(n, n + 4)] else []).

(** vlan_add only appends, and only below max. *)
Lemma vlan_add_len : forall t max p v, Z.of_nat (length t) <= max ->
  (length t <= length (snd (vlan_add t max p v)))%nat /\ Z.of_nat (length (snd (vlan_add t max p v))) <= max.
Proof.
  intros t max p v H. unfold vlan_add.
  match goal with |- context [if existsb ?f ?l then _ else _] => destruct (existsb f l) end; [cbn [snd]; lia|].
  destruct (max <=? Z.of_nat (length t)) eqn:E; [cbn [snd]; lia|].
  apply Z.leb_gt in E. cbn [snd]. rewrite length_app. cbn [length]. lia.
Qed.

(** On W only: when the table grows from t to t' within max entries, and the frames and *n lie apart
    from the block tab[0 .. max], every address of W lies below the guard entry tab[max] or past the block. *)
Lemma vtab_W_spares_guard : forall depth sp lo tab n max t t' a,
  (length t <= length t')%nat -> Z.of_nat (length t') <= max -> lo + depth <= sp ->
  apart tab (RVLAN_SIZE * (max + 1)) lo sp -> apart n 4 tab (tab + RVLAN_SIZE * (max + 1)) ->
  ~ outside (vtab_W depth sp tab n t t') a ->
  a < tab + RVLAN_SIZE * max \/ tab + RVLAN_SIZE * (max + 1) <= a.
Proof.
  intros depth sp lo tab n max t t' a L1 L2 Hd Ht Hn Hin. unfold apart, RVLAN_SIZE in *.
  destruct (Z_lt_le_dec a (tab + 18 * max)) as [H|H]; [left; exact H|].
  destruct (Z_lt_le_dec a (tab + 18 * (max + 1))) as [H'|H']; [|right; exact H'].
  exfalso. apply Hin. unfold vtab_W, RVLAN_SIZE.
  destruct (length t <? length t')%nat; cbn [app outside]; repeat split; lia.
Qed.

(** So the guard entry is untouched by munch. *)
Lemma vtab_W_guard : forall depth sp lo tab n max t t' (m m' : word -> option byte),
  (length t <= length t')%nat -> Z.of_nat (length t') <= max -> lo + depth <= sp ->
  apart tab (RVLAN_SIZE * (max + 1)) lo sp -> apart n 4 tab (tab + RVLAN_SIZE * (max + 1)) ->
  munch (vtab_W depth sp tab n t t') m m' -> guard_at rsegs m tab max -> guard_at rsegs m' tab max.
Proof.
  intros depth sp lo tab n max t t' m m' L1 L2 Hd Ht Hn Hm Hg. unfold guard_at in *.
  eapply bytes_at_transport; [exact Hg | exact Hm |].
  change (Z.of_nat (length GUARD_BYTES)) with 18. unfold vtab_W, apart, RVLAN_SIZE in *.
  destruct (length t <? length t')%nat; cbn [app disjoint_from]; repeat split; lia.
Qed.

Lemma add_W_spares_guard : forall sp lo tab n max t p vid a,
  Z.of_nat (length t) <= max -> lo + ADD_STACK <= sp ->
  apart tab (RVLAN_SIZE * (max + 1)) lo sp -> apart n 4 tab (tab + RVLAN_SIZE * (max + 1)) ->
  ~ outside (vtab_W ADD_STACK sp tab n t (snd (vlan_add t max p vid))) a ->
  a < tab + RVLAN_SIZE * max \/ tab + RVLAN_SIZE * (max + 1) <= a.
Proof.
  intros sp lo tab n max t p vid a H Hd Ht Hn Hin. destruct (vlan_add_len t max p vid H) as [L1 L2].
  exact (vtab_W_spares_guard _ _ _ _ _ _ _ _ _ L1 L2 Hd Ht Hn Hin).
Qed.

Lemma add_guard_kept : forall sp lo tab n max t p vid (m m' : word -> option byte),
  Z.of_nat (length t) <= max -> lo + ADD_STACK <= sp ->
  apart tab (RVLAN_SIZE * (max + 1)) lo sp -> apart n 4 tab (tab + RVLAN_SIZE * (max + 1)) ->
  munch (vtab_W ADD_STACK sp tab n t (snd (vlan_add t max p vid))) m m' ->
  guard_at rsegs m tab max -> guard_at rsegs m' tab max.
Proof.
  intros sp lo tab n max t p vid m m' H Hd Ht Hn Hm Hg. destruct (vlan_add_len t max p vid H) as [L1 L2].
  exact (vtab_W_guard _ _ _ _ _ _ _ _ _ _ L1 L2 Hd Ht Hn Hm Hg).
Qed.

Definition reac_declared_vlan_add_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (t : list (list Z * Z)) (p : list Z),
    add_pre m (bv_unsigned sp) lo (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned a3)
      (bv_unsigned a4) t p ->
    evt rsegs
      (ret_post rsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
         (fst (vlan_add t (bv_unsigned a1) p (bv_unsigned a4)))
         m
         (vtab_W ADD_STACK (bv_unsigned sp) (bv_unsigned a0) (bv_unsigned a2) t
            (snd (vlan_add t (bv_unsigned a1) p (bv_unsigned a4))))
         lo
         (fun m' => rtab_at rsegs m' (bv_unsigned a0) (snd (vlan_add t (bv_unsigned a1) p (bv_unsigned a4))) /\
                   rw_cells rsegs m' (bv_unsigned a2)
                     [C4 (Z_to_bv 64 (Z.of_nat (length (snd (vlan_add t (bv_unsigned a1) p (bv_unsigned a4))))))]))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_DECLARED_VLAN_ADD) fc None m (seg_rom rsegs)).
