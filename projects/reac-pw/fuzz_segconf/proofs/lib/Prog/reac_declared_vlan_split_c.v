From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import seg_env.
Import ListNotations.
Open Scope Z_scope.

(** reac_declared_vlan_split(segment, parent, cap, vid) (reac_declared_vlan.c:32-62; at 0x15a94 in the image
    3776ca44d75c; 300 bytes, frame 64 bytes, saves ra and s0-s5).
    As compiled: 0 when segment, parent, cap or vid is 0 (four `beqz`; the premise excludes them); dot =
    strrchr(segment, '.') (`jal` 0x15ae0); 0 when dot is NULL, dot = segment or dot[1] = 0;
    the digit loop (0x15b08 .. `bnez a1` 0x15b18) returns 0 at a byte with `a1 - 0x30 >u 9`
    and leaves a1 = 0 at its exit, so strtol(dot + 1, NULL, 10) (`jal` 0x15b20) gets its NULL end pointer with no
    `li a1, 0`; v outside [1, 4094] returns 0 (`v - 4095 >=u -4094` fails, `bgeu` 0x15b38); plen = dot - segment,
    0 when plen + 1 >u cap or plen + 1 >u 16 (`bltu` 0x15b70, 0x15b78); strlen(segment) (`jal` 0x15b80), 0 when it is
    >= 16 (`len - 16 <u -17`, 0x15b8c); memcpy(parent, segment, plen) (`jal` 0x15b9c) and parent[plen] = 0 (`sb`
    0x15ba4); name_ok(parent) (`jal` 0x15bac) = 0 returns 0; else *vid = v (`sh s5,0(s0)` 0x15bb4) and it returns 1.
    It reads the segment's bytes, its NUL and the slack to the next 8-byte boundary (strrchr and strlen read words),
    the errno cell and the stack-protector cells (strtol). It writes its frame and the callee frames
    [sp - SPLIT_STACK, sp), the errno cell [tp - 164, tp - 160) (strtol_null_contract's munch holds it), parent[0 ..
    plen] when it reaches the memcpy (split_copy: every test before name_ok passed), and *vid when it returns 1. The
    errno cell keeps its value ev: strtol runs only on a tail of 1 to 13 digits (length s < 16), so __intscan sets
    neither EINVAL (no digit) nor ERANGE (out of range): Prog/__intscan_c.v's s10_errno str ev = ev when s10_nd str <>
    0 and s10_inrange str.

    Post in the spine's terms: a0 = 1, parent holds the C string p and *vid = v (the uint16_t) when
    SegModel.vlan_split s = Some (p, v); a0 = 0 when it is None; the errno cell holds ev as before. The spine states
    vlan_split for cap = IFNAMSIZ = 16 (SegModel.v:764), the only value a caller passes, so the premise is cap = 16.
    vlan_split_copy: on Some (p, v), p = firstn di s for the di of split_copy, so W holds the parent bytes the post
    names.

    Callee contracts its walk takes as premises:
    - strrchr_contract (Prog/strrchr_c.v, STRRCHR = 0x1ef60, STRRCHR_K = 32; commit
      65bf41870056): the string, its NUL and its slack apart from its 32 bytes of stack;
    - strtol_null_contract (Prog/strtol_null_c.v, STRTOL = 0x1dc9c; commit
      06702a5f1f22): the tail and its NUL below 2^64 - 1, 368 bytes of stack, the errno cell rw_cells (tp - 164) [C4
      ev], the stack-protector GOT cell and guard (seg_env.ssp_ok), each apart from the stack, the errno cell apart
      from the guard;
    - strlen_contract (Prog/strlen_c.v, STRLEN = 0x1ec30): the string and its slack;
    - memcpy_contract (Prog/memcpy_c.v, 0x1e52c): parent's 16 bytes present and writable, apart from the segment;
    - name_ok_contract (Prog/name_ok_c.v, NAME_OK = 0x15bc0): its 48 bytes of stack.
    SPLIT_STACK = 64 + 368: strtol's need is the largest (strrchr 32, name_ok 48, strlen and memcpy none).

    Call site: reac_segconf_declared 0x15a20 (reac_segconf.c:572) with a0 = &c->seg[i].name = c + 356 i (the 16-byte
    name field holds the name and its NUL, length < 16 by rconf_enc's cstr_enc 16, and its slack lies inside the
    356-byte entry; c, the reader's block, is apart from the stack), a1 = parent = declared's sp + 0x10 (16 bytes of
    its frame), a2 = 16, a3 = vid = declared's sp + 0xe (2-aligned: sp is 16-aligned); parent and vid lie above this
    sp; tp, the errno cell (apart from the stack, from the c block and from the table block) and the stack-protector
    cells as declared received them. *)
Definition REAC_DECLARED_VLAN_SPLIT : Z := 0x15a94.
Definition SPLIT_STACK : Z := 64 + 368.

(** The parent length split copies: [Some di], dot = segment + di, when every test before name_ok passes (the
    prefix of SegModel.vlan_split, V:36-55); it then writes parent[0 .. di] (memcpy and the NUL). *)
Definition split_copy (s : list Z) : option nat :=
  match strrchr s DOT with
  | None => None
  | Some di =>
    if (di =? 0)%nat || (hd0 (skipn (S di) s) =? 0) then None else
    let tail := cut_nul (skipn (S di) s) in
    if negb (forallb isdigit tail) then None else
    let v := strtol10 tail in
    if (v <? 1) || (4094 <? v) then None else
    if (16 <? di + 1)%nat || (16 <? di + 1)%nat then None else
    if (16 <? strlen s + 1)%nat then None else Some di
  end.

Lemma vlan_split_copy : forall s p v,
  vlan_split s = Some (p, v) -> exists di, split_copy s = Some di /\ p = firstn di s.
Proof.
  intros s p v. unfold vlan_split, split_copy.
  destruct (strrchr s DOT) as [di|]; [|intros H; discriminate H]. cbv zeta.
  repeat match goal with
  | |- context [if ?b then _ else _] => destruct b
  end; intros H; try discriminate H.
  injection H as <- _. exists di. split; reflexivity.
Qed.

(** The errno cell strtol may write (tp - 164, __errno_location's cell: strtol_null_c.v), a present writable int
    holding ev, apart from the stack region [lo, sp) and from the stack-protector guard. *)
Definition errno_ok (m : word -> option byte) (sp lo tp : Z) (ev : word) : Prop :=
  rw_cells rsegs m (tp - 164) [C4 ev] /\ apart (tp - 164) 4 lo sp /\
  apart (tp - 164) 4 (sa_guard SA) (sa_guard SA + 8).

(** tp, the thread pointer, comes after lo: strtol's errno cell is at tp - 164, in W, so it is apart from the objects
    the caller passes (segment, parent, vid) as well as from the stack. The segment's extent apart from the stack and
    from parent is its string, its NUL and 7 bytes (the slack strrchr and strlen read is at most 7). The stack region
    lies above the image (seg_env.SA's sa_img_end), so apart from the stack-protector cells. *)
Definition split_pre (m : word -> option byte) (sp lo tp segment parent cap vid : Z) (s : list Z) (ev : word)
    : Prop :=
  segment <> 0 /\ cstr_at rsegs m segment s /\ (length s < 16)%nat /\
  segment + Z.of_nat (length s) + 8 <= 2 ^ 64 /\ apart segment (Z.of_nat (length s) + 8) lo sp /\
  parent <> 0 /\ cap = 16 /\ (exists pb, rw_cells rsegs m parent [CB 16 pb]) /\ apart parent 16 lo sp /\
  apart segment (Z.of_nat (length s) + 8) parent (parent + 16) /\
  vid <> 0 /\ vid mod 2 = 0 /\ wr_at rsegs m vid 2 /\ apart vid 2 lo sp /\ apart vid 2 parent (parent + 16) /\
  errno_ok m sp lo tp ev /\ apart (tp - 164) 4 segment (segment + Z.of_nat (length s) + 8) /\
  apart (tp - 164) 4 parent (parent + 16) /\ apart (tp - 164) 4 vid (vid + 2) /\
  ssp_ok m /\ sa_img_end SA <= lo /\
  stack_ok rsegs m lo sp SPLIT_STACK /\ mem_inv rsegs m.

(** The bytes it writes: the frames, the errno cell, parent[0 .. di] when it copies, *vid when it returns 1. *)
Definition split_W (sp tp parent vid : Z) (s : list Z) : list ivl :=
  [(sp - SPLIT_STACK, sp); (tp - 164, tp - 164 + 4)] ++
  match split_copy s with Some di => [(parent, parent + Z.of_nat di + 1)] | None => [] end ++
  match vlan_split s with Some _ => [(vid, vid + 2)] | None => [] end.

Definition reac_declared_vlan_split_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (s : list Z) (ev : word),
    split_pre m (bv_unsigned sp) lo (bv_unsigned tp) (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2)
      (bv_unsigned a3) s ev ->
    evt rsegs
      (ret_post rsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
         (match vlan_split s with Some _ => 1 | None => 0 end)
         m
         (split_W (bv_unsigned sp) (bv_unsigned tp) (bv_unsigned a1) (bv_unsigned a3) s)
         lo
         (fun m' => rw_cells rsegs m' (bv_unsigned tp - 164) [C4 ev] /\
           match vlan_split s with
           | Some (p, v) => cstrz_at rsegs m' (bv_unsigned a1) p /\
                            bytes_at rsegs m' (bv_unsigned a3) (le2 (Z_to_bv 64 v))
           | None => True
           end))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_DECLARED_VLAN_SPLIT) fc None m (seg_rom rsegs)).
