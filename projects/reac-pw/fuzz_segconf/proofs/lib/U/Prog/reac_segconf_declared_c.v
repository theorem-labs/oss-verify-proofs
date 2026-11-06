From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import seg_env.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import reac_declared_vlan_split_c reac_declared_vlan_add_c.
Import ListNotations.
Open Scope Z_scope.

(** reac_segconf_declared(c, tab, max, n) (reac_segconf.c:561-580; at 0x16210 in the UBSan image 1696d6c34ffd;
    296 bytes, frame 112 bytes, saves ra and s0-s9; parent[16] at
    sp + 8, vid at sp + 6).
    As compiled: c = NULL returns 0 (`beqz a0`); `andi a0, 7` traps a misaligned c; s5 = &c->n (c + 0x2c80)
    and `lw`/`blez` return 0 for n <= 0; the loop (head 0x16284, latch `blt s7, a0` 0x162e8, c->n reloaded each pass;
    s3 = &seg[i], s7 = i, s6 = 356 i, s4 = added)
    skips seg[i] when `lw 0x18(s3)` (ignore) is nonzero, else calls reac_declared_vlan_split(&seg[i].name, sp + 8,
    16, sp + 6) (`jal` 0x162a4); on 1 it loads the vid (`lhu`) and calls reac_declared_vlan_add(tab, max, n,
    sp + 8, vid) (`jal` 0x162c0); a negative result returns -1, else added += r. It returns added (`add`, checked
    against `addw`), or -1 (`bltz` 0x162c4 -> s4 = -1), in a0 (`sext.w a0, s4`). The UBSan checks (to the `unimp` at
    0x16334): 0x1624c c & 7 <> 0 (alignment): c mod 16 = 0; 0x16284 i = 32 (array-bounds): i < c->n <= 32
    (rconf_enc); 0x16288 ~c <u 356 i (pointer-overflow): c + 16616 <= 2^64 (rconf_at's bytes_at); 0x162d4 added + r
    <> its 32-bit sign extension (signed-integer-overflow): added <= i <= 32 and r is 0 or 1. The traps of split and
    add fall through by their premises, which this premise gives. It reads c->n, seg[i].ignore and seg[i].name for i
    < n, the table entries and *n (in add), the errno cell and the stack-protector cells (in strtol). It writes its
    frame and the callee frames, [sp - DECLARED_STACK, sp), the errno cell [tp - 164, tp - 160) (in split's strtol;
    it keeps its value ev, reac_declared_vlan_split_c.v), the entries it appends, [tab + 18 length tb, tab + 18
    length tb'), and *n when the table grows: never the guard entry tab[max] (lemmas
    declared_W_spares_guard, declared_guard_kept).

    Post in the spine's terms: a0 = fst (SegModel.r_declared rc tb max) (-1 is the word 2^64 - 1, ret_post's
    Z_to_bv 64), the table holds tb' = snd (r_declared rc tb max) (seg_spec.rtab_at), *n = length tb', and the errno
    cell holds ev as before.
    Loop invariant, at the head: r_decl_go (skipn i (rc_seg rc)) ti max added = r_decl_go
    (rc_seg rc) tb max 0, with ti the table in memory (rtab_at, *n = length ti, its free entries writable) and added
    in s4.

    Callee contracts its walk takes as premises: reac_declared_vlan_split_contract (Prog/reac_declared_vlan_split_c.v
    under lib/U, 0x16338) and reac_declared_vlan_add_contract (Prog/reac_declared_vlan_add_c.v under
    lib/U, 0x16530). At the split call: segment = c + 356 i (cstr_at from rconf_at: the 16-byte name field
    holds the name and its NUL, length < 16, and the slack lies inside the entry; c + 356 i + 23 < c + 16616), parent
    and vid in this frame (sp 16-aligned, so vid is 2-aligned), the errno cell holding ev (split's post keeps it;
    adds write only table entries and *n, apart from it), the stack-protector cells as received (the adds write above
    sa_img_end), split's stack below sp - 112. At the add call: vtab_pre of the current table, parent the C string
    split left (its slack is the rest of the 16-byte buffer, inside [lo, sp) and apart from the block), vid < 2^16.
    DECLARED_STACK = 112 + SPLIT_STACK (split's need, 432, is above add's).

    Call site: LLVMFuzzerTestOneInput 0x141c8 (fuzz_segconf.c:664) with a0 = c (the reader's malloc(16616) block,
    ld 0x48(sp)), a1 = tab = calloc(cap + 1, 18) (ld 0(sp), the calloc at 0x13e7c: nonzero, 16-aligned, zeroed;
    tab[cap] set to 0x5a x 18 by the memset at 0x13eb8), a2 = cap = u8 % 40 (ld 0x10(sp)), a3 = &n = sp + 0x5c
    (main's int cell: 1 when flags & 1 and cap > 0, else 0); tb = SegModel.vlan_init p, so length tb <= cap, and the
    free entries [length tb, cap) hold calloc's zeros. The heap blocks and main's frame lie above the image and apart
    from [lo, sp). Its post, with declared_guard_kept, gives check_declared's premise (0x141e8): rtab_at of tb',
    guard_at tab cap, n = length tb'. *)
Definition REAC_SEGCONF_DECLARED : Z := 0x16210.
Definition DECLARED_STACK : Z := 112 + SPLIT_STACK.

(** c the reader's block holding rc; the table and *n (vtab_pre) apart from c; the errno cell (errno_ok, holding ev)
    apart from c, the table block and *n, as every object a caller passes is (it is in W); the table block outside the image's reserved segments (blk_noimg), *n and the
    stack region above the image (sa_img_end), so the adds and the frames miss the stack-protector cells strtol reads.
    tp comes after lo, as in split_pre. *)
Definition declared_pre (m : word -> option byte) (sp lo tp c tab max n : Z) (rc : rconf) (tb : list (list Z * Z))
    (ev : word) : Prop :=
  c <> 0 /\ c mod 16 = 0 /\ rconf_at rsegs m c rc /\ apart c SEG_C_SIZE lo sp /\
  vtab_pre m sp lo tab max n tb /\
  apart c SEG_C_SIZE tab (tab + RVLAN_SIZE * (max + 1)) /\ apart n 4 c (c + SEG_C_SIZE) /\
  errno_ok m sp lo tp ev /\ apart (tp - 164) 4 c (c + SEG_C_SIZE) /\
  apart (tp - 164) 4 tab (tab + RVLAN_SIZE * (max + 1)) /\ apart (tp - 164) 4 n (n + 4) /\
  ssp_ok m /\ sa_img_end SA <= lo /\ blk_noimg rsegs tab (RVLAN_SIZE * (max + 1)) /\ sa_img_end SA <= n /\
  stack_ok rsegs m lo sp DECLARED_STACK /\ mem_inv rsegs m.

(** The bytes it writes: vtab_W's (the frames, the appended entries, *n when the table grew) and the errno cell. *)
Definition declared_W (sp tp tab n : Z) (tb tb' : list (list Z * Z)) : list ivl :=
  vtab_W DECLARED_STACK sp tab n tb tb' ++ [(tp - 164, tp - 164 + 4)].

(** r_declared only appends, and only below max. *)
Lemma r_decl_go_len : forall segs t max added, Z.of_nat (length t) <= max ->
  (length t <= length (snd (r_decl_go segs t max added)))%nat /\
  Z.of_nat (length (snd (r_decl_go segs t max added))) <= max.
Proof.
  induction segs as [|s r IH]; intros t max added H; cbn [r_decl_go]; [cbn [snd]; lia|].
  destruct (rs_ignore s); [apply IH; exact H|].
  destruct (vlan_split (rs_name s)) as [[p v]|]; [|apply IH; exact H].
  destruct (vlan_add t max p v) as [rv t'] eqn:E.
  pose proof (vlan_add_len t max p v H) as L. rewrite E in L. cbn [snd] in L.
  destruct (rv <? 0); [cbn [snd]; exact L|].
  destruct (IH t' max (added + rv) (proj2 L)) as [A1 A2]. split; [lia | exact A2].
Qed.

(** For reac_segconf_declared, on W only: every address of W lies below the guard entry tab[max] or
    past the block tab[0 .. max]. *)
Lemma declared_W_spares_guard : forall sp lo tp tab n max rc tb a,
  Z.of_nat (length tb) <= max -> lo + DECLARED_STACK <= sp ->
  apart tab (RVLAN_SIZE * (max + 1)) lo sp -> apart n 4 tab (tab + RVLAN_SIZE * (max + 1)) ->
  apart (tp - 164) 4 tab (tab + RVLAN_SIZE * (max + 1)) ->
  ~ outside (declared_W sp tp tab n tb (snd (r_declared rc tb max))) a ->
  a < tab + RVLAN_SIZE * max \/ tab + RVLAN_SIZE * (max + 1) <= a.
Proof.
  intros sp lo tp tab n max rc tb a H Hd Ht Hn He Hin. unfold r_declared in Hin.
  destruct (r_decl_go_len (rc_seg rc) tb max 0 H) as [L1 L2]. unfold apart, RVLAN_SIZE in *.
  destruct (Z_lt_le_dec a (tab + 18 * max)) as [H1|H1]; [left; exact H1|].
  destruct (Z_lt_le_dec a (tab + 18 * (max + 1))) as [H2|H2]; [|right; exact H2].
  exfalso. apply Hin. unfold declared_W, vtab_W, RVLAN_SIZE.
  match goal with |- context [if ?b then _ else _] => destruct b end; cbn [app outside]; repeat split; lia.
Qed.

(** So the guard entry is untouched by munch. *)
Lemma declared_guard_kept : forall sp lo tp tab n max rc tb (m m' : word -> option byte),
  Z.of_nat (length tb) <= max -> lo + DECLARED_STACK <= sp ->
  apart tab (RVLAN_SIZE * (max + 1)) lo sp -> apart n 4 tab (tab + RVLAN_SIZE * (max + 1)) ->
  apart (tp - 164) 4 tab (tab + RVLAN_SIZE * (max + 1)) ->
  munch (declared_W sp tp tab n tb (snd (r_declared rc tb max))) m m' ->
  guard_at rsegs m tab max -> guard_at rsegs m' tab max.
Proof.
  intros sp lo tp tab n max rc tb m m' H Hd Ht Hn He Hm Hg. unfold r_declared in Hm.
  destruct (r_decl_go_len (rc_seg rc) tb max 0 H) as [L1 L2]. unfold guard_at in *.
  eapply bytes_at_transport; [exact Hg | exact Hm |].
  change (Z.of_nat (length GUARD_BYTES)) with 18. unfold declared_W, vtab_W, apart, RVLAN_SIZE in *.
  match goal with |- context [if ?b then _ else _] => destruct b end; cbn [app disjoint_from]; repeat split; lia.
Qed.

Definition reac_segconf_declared_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (rc : rconf) (tb : list (list Z * Z))
         (ev : word),
    declared_pre m (bv_unsigned sp) lo (bv_unsigned tp) (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2)
      (bv_unsigned a3) rc tb ev ->
    evt rsegs
      (ret_post rsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
         (fst (r_declared rc tb (bv_unsigned a2)))
         m
         (declared_W (bv_unsigned sp) (bv_unsigned tp) (bv_unsigned a1) (bv_unsigned a3) tb
            (snd (r_declared rc tb (bv_unsigned a2))))
         lo
         (fun m' => rtab_at rsegs m' (bv_unsigned a1) (snd (r_declared rc tb (bv_unsigned a2))) /\
                   rw_cells rsegs m' (bv_unsigned a3)
                     [C4 (Z_to_bv 64 (Z.of_nat (length (snd (r_declared rc tb (bv_unsigned a2))))))] /\
                   rw_cells rsegs m' (bv_unsigned tp - 164) [C4 ev]))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_SEGCONF_DECLARED) fc None m (seg_rom rsegs)).
