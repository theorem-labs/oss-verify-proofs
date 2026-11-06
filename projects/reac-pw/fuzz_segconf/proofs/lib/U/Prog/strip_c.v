From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
Import ListNotations.
Open Scope Z_scope.

(** strip(&s, &e) (fuzz_segconf.c:118-125; at 0x15028 in the UBSan image 1696d6c34ffd, size 176, read with a
    disassembler from the unstripped twin afc060e3cc9c; a leaf: no frame, no stack access, no call).
    The plain build has no such function: clang inlines strip into m_file at its five sites, so there is no plain
    contract.
    As compiled (a0 = sc = &s, a1 = ec = &e): (sc | ec) & 7 <> 0 traps (0x15030); a3 = *s, a2 = *e (`ld`
    0x15034-0x15038); *s >= *e returns (`bgeu` 0x1503c to the `ret` at 0x150d0). Forward loop (0x15058-0x15084):
    *s = 0 traps; the byte **s (`lbu` 0x1505c) is blank when it is <= 32 and bit **s of 0x100002200 is set (space,
    tab, CR: SegModel.blank); not blank leaves to the back loop; else *s + 1 is checked against wrapping (0x15074),
    stored (`sd a3,0(a0)` 0x1507c), *e reloaded (0x15080), and the loop goes on while *s < *e, else returns. Back loop
    (0x1508c-0x150cc): *e = 1 traps; the byte at *e - 1 (`lbu -1(a2)` 0x15094) not blank returns; else *e < 2 traps,
    *e - 1 is stored (`sd a2,0(a1)` 0x150c4), *s reloaded (0x150c8), and the loop goes on while *s < *e, else
    returns.
    It reads the two cells and the bytes [s0, e0); it writes only the two cells.
    UBSan traps (all to the `unimp` at 0x150d4): 0x15030 alignment (sc | ec) & 7 (both cells 8-aligned); 0x15058
    `beqz a3`, *s = 0 (s0 > 0 and *s only grows); 0x15074 `bgeu 1,a7` with a7 = *s + 1 (since *s + 1 <= e0 < 2^64
    and *s >= s0 > 0); 0x15090 `beq a2,1` and 0x150bc `bltu a2,2`, *e = 1 or *e - 1 wrapping (in the back loop
    *e > *s >= s0 >= 1, so *e >= 2).

    Post in the spine's terms: the cell s holds s0 + strip_lead l and the cell e holds e0 - strip_trail l, with l
    the bytes [s0, e0) (zs); [strip_mid] below: the bytes between the two new pointers are SegModel.h_strip l, and
    [strip_le]: s0 + strip_lead l <= e0 - strip_trail l.

    No callee.

    Call sites: m_file, five. At each, the two cells are distinct 8-aligned slots of m_file's frame (272 bytes; above
    strip's sp, which is m_file's), holding pointers into the text block (a heap block: nonzero, s0 <= e0, outside
    the frame): 0x14410 (c:285: &s = sp + 0x40, &e = sp + 0x38, the line [s, e) after the comment cut), 0x14470
    (c:167: sp + 0x48, sp + 0xa0, the header between '[' and ']'), 0x144d0 (c:173: sp + 0x98, sp + 0x90, the name
    after "segment"), 0x14564 (c:205: sp + 0xa0, sp + 0x98, the key before '='), 0x14570 (c:206: sp + 0x90,
    sp + 0x88, the value after '='). *)
Definition STRIP : Z := 0x15028.
Definition STRIP_STACK : Z := 0.

(** The leading blanks, and the trailing blanks of what is left after them. *)
Definition strip_lead (l : list Z) : nat := length (takewhile blank l).
Definition strip_trail (l : list Z) : nat := length (takewhile blank (rev (dropwhile blank l))).

Definition strip_pre (m : word -> option byte) (sp lo sc ec : Z) (s0 e0 : Z) (l : list byte) : Prop :=
  sc mod 8 = 0 /\ ec mod 8 = 0 /\ apart sc 8 ec (ec + 8) /\
  rw_cells rsegs m sc [C8 (Z_to_bv 64 s0)] /\ apart sc 8 lo sp /\
  rw_cells rsegs m ec [C8 (Z_to_bv 64 e0)] /\ apart ec 8 lo sp /\
  0 < s0 <= e0 /\ e0 < 2 ^ 64 /\ bytes_at rsegs m s0 l /\ Z.of_nat (length l) = e0 - s0 /\
  apart s0 (e0 - s0) sc (sc + 8) /\ apart s0 (e0 - s0) ec (ec + 8) /\
  stack_ok rsegs m lo sp STRIP_STACK /\ mem_inv rsegs m.

Definition strip_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (sv ev : Z) (l : list byte),
    strip_pre m (bv_unsigned sp) lo (bv_unsigned a0) (bv_unsigned a1) sv ev l ->
    evt rsegs
      (ret_void rsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
         m
         ([(bv_unsigned a0, bv_unsigned a0 + 8); (bv_unsigned a1, bv_unsigned a1 + 8)])
         lo
         (fun m' => bytes_at rsegs m' (bv_unsigned a0) (le8 (Z_to_bv 64 (sv + Z.of_nat (strip_lead (zs l))))) /\
                    bytes_at rsegs m' (bv_unsigned a1) (le8 (Z_to_bv 64 (ev - Z.of_nat (strip_trail (zs l)))))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 STRIP) fc None m (seg_rom rsegs)).

(** ** Facts about the post (pure lists) *)
Lemma dropwhile_skipn (P : Z -> bool) (l : list Z) : dropwhile P l = skipn (length (takewhile P l)) l.
Proof. induction l as [|b r IH]; cbn; [reflexivity|]. destruct (P b); cbn; [exact IH | reflexivity]. Qed.

Lemma takewhile_le (P : Z -> bool) (l : list Z) : (length (takewhile P l) <= length l)%nat.
Proof. induction l as [|b r IH]; cbn; [lia|]. destruct (P b); cbn; lia. Qed.

Lemma dropwhile_length (P : Z -> bool) (l : list Z) :
  length (dropwhile P l) = (length l - length (takewhile P l))%nat.
Proof. rewrite dropwhile_skipn, length_skipn. reflexivity. Qed.

(** The bytes between the two new pointers are h_strip of the bytes. *)
Lemma strip_mid (l : list Z) :
  firstn (length l - strip_lead l - strip_trail l) (skipn (strip_lead l) l) = h_strip l.
Proof.
  unfold strip_lead, strip_trail, h_strip.
  rewrite (dropwhile_skipn blank (rev (dropwhile blank l))).
  rewrite skipn_rev, rev_involutive.
  remember (length (takewhile blank (rev (dropwhile blank l)))) as t eqn:Et. clear Et.
  rewrite (dropwhile_skipn blank l), length_skipn. reflexivity.
Qed.

(** The new s is at most the new e. *)
Lemma strip_le (l : list Z) : (strip_lead l + strip_trail l <= length l)%nat.
Proof.
  unfold strip_lead, strip_trail.
  pose proof (takewhile_le blank (rev (dropwhile blank l))) as H1. rewrite length_rev in H1.
  pose proof (dropwhile_length blank l) as H2. pose proof (takewhile_le blank l) as H3. lia.
Qed.
