(* The slot LLVMFuzzerTestOneInput (fuzz_link.c:764-790), plain image: the facts every piece of its walk
   shares. Pure and machine-level only (no allocator): the program points, the frame layout, the interface
   table interfaces() builds, the inlined name_of, and the loop-head state of the 48-operation loop.

   Every address and offset below is read from the plain image (the unstripped twin of the pin
   ebe34b259b9f; link/ct/dis/plain/LLVMFuzzerTestOneInput.s, link/functions.tsv). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import printf_facts_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Regs6ss.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Program points (plain)
   ========================================================================== *)

Definition L_ENTRY : Z := 0x1384c.      (* addi sp, sp, -0x1e0 *)
Definition L_CALLOC1 : Z := 0x13994.    (* jal calloc (1, 8856), ra 0x13998 *)
Definition L_CALLOC1_RA : Z := 0x13998.
Definition L_CALLOC2 : Z := 0x139a4.    (* jal calloc (1, 516), ra 0x139a8 *)
Definition L_CALLOC2_RA : Z := 0x139a8.
Definition L_LH : Z := 0x13a1c.         (* the loop head: ld a2, 0x40(sp) *)
Definition L_TAIL : Z := 0x1406c.       (* ld s2, 0x48(sp); addiw s11, s11, 1; bnez s2, L_LH *)
Definition L_EXIT : Z := 0x1413c.       (* free (marks); free (m); return 0 *)
Definition L_RET0 : Z := 0x1414c.       (* mv a0, zero; the epilogue *)
Definition L_ABORT : Z := 0x1418c.      (* jal abort: the harness's own calloc failure *)

(* the jump table at 0x106b0 (5 x int32, read from the image) and the default arm *)
Definition A_JT : Z := 0x106b0.
Definition L_OP0 : Z := 0x13a68.        (* op_read *)
Definition L_OP1 : Z := 0x13bcc.        (* op_write *)
Definition L_OP2 : Z := 0x13afc.        (* op_mark *)
Definition L_OP3 : Z := 0x13b24.        (* op_unmark *)
Definition L_OP4 : Z := 0x13a9c.        (* op_decide *)
Definition L_OP5 : Z := 0x13bf4.        (* op_refused (op byte % 6 = 5) *)

Definition op_pc (op : Z) : Z :=
  if op =? 0 then L_OP0 else if op =? 1 then L_OP1 else if op =? 2 then L_OP2
  else if op =? 3 then L_OP3 else if op =? 4 then L_OP4 else L_OP5.

(* ==========================================================================
   2. The frame: 480 bytes at S - 480 (S = sp at entry)
   ========================================================================== *)

Definition SLOT_FRAME : Z := 480.
Definition SLOT_STACK_Z : Z := 65536.   (* FrameAPI.SLOT_STACK *)

(* offsets from the frame base sp = S - 480 *)
Definition FO_ODD : Z := 8.        (* &odd[0] = 0x207c0 *)
Definition FO_MARK0 : Z := 16.     (* m + 8340 = &m->mark[0] *)
Definition FO_EMPTY : Z := 24.     (* 0x10368, "" *)
Definition FO_MARKS : Z := 32.     (* marks *)
Definition FO_GNAMES : Z := 40.    (* g_names = 0x741f8 *)
Definition FO_JT : Z := 48.        (* the jump table 0x106b0 *)
Definition FO_GNL42 : Z := 56.     (* g_nl + 0x42000 *)
Definition FO_P : Z := 64.         (* in.p *)
Definition FO_N : Z := 72.         (* in.n *)
Definition FO_B40 : Z := 80.       (* 40 bytes: wa / kind[32] / the decide `ok` cell at 0x50 *)
Definition FO_B256 : Z := 120.     (* 256 bytes: wk / alias[256] / own cell at 0x78 *)
Definition FO_SAVED : Z := 376.    (* s11 .. s0, ra: 104 bytes, = S - 104 *)

Definition GNL40 : Z := A_G_NL + 0x40000.   (* s1 *)
Definition GNL42 : Z := A_G_NL + 0x42000.   (* the frame cell at 0x38 *)

(* the frame's cells at the loop head: three cells the code never reads before it writes them, the
   eight pointer cells, the cursor, the two buffers *)
Definition lh_cells (md mk P N : Z) (j0 j1 j2 : list byte) : list cell :=
  [CB 8 j0; C8 (wz A_ODD); C8 (wz (md + MD_MARK)); C8 (wz A_EMPTY); C8 (wz mk); C8 (wz A_G_NAMES);
   C8 (wz A_JT); C8 (wz GNL42); C8 (wz P); C8 (wz N); CB 40 j1; CB 256 j2].

(* the 104 bytes of the callee-saved registers and ra, as the prologue stores them at S - 104 *)
Definition saved_bytes (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list byte :=
  le8 s11 ++ le8 s10 ++ le8 s9 ++ le8 s8 ++ le8 s7 ++ le8 s6 ++ le8 s5 ++ le8 s4 ++ le8 s3 ++ le8 s2 ++
  le8 s1 ++ le8 s0 ++ le8 ra.

(* ==========================================================================
   3. The interface table interfaces() builds (fuzz_link.c:86-100)
   ========================================================================== *)

(* the decimal digits of 0 <= k < 100, as printf's %d writes them *)
Definition dec2 (k : Z) : list Z := if k <? 10 then [48 + k] else [48 + k / 10; 48 + k mod 10].

(* g_names[k] = "nl<k>" *)
Definition gname_z (k : Z) : list Z := 110 :: 108 :: dec2 k.
Definition gname (k : Z) : list byte := map zb (gname_z k).

(* odd[] (0x207c0, 6 pointers into .rodata) and the strings they point at *)
Definition S_ENP : list byte := map zb [101; 110; 112; 49; 51; 49; 115; 48; 46; 51; 51].   (* enp131s0.33 *)
Definition S_ETH0 : list byte := map zb [101; 116; 104; 48].                              (* eth0 *)
Definition S_WLAN0 : list byte := map zb [119; 108; 97; 110; 48].                         (* wlan0 *)
Definition S_VETH : list byte := map zb [118; 101; 116; 104; 45; 98; 111; 120].           (* veth-box *)
Definition S_GONE0 : list byte := map zb [103; 111; 110; 101; 48].                        (* gone0 *)
Definition odd_ptrs : list Z := [0x10368; 0x1039c; 0x1056a; 0x103bc; 0x10598; 0x102a2].
Definition odd_strs : list (list byte) := [[]; S_ENP; S_ETH0; S_WLAN0; S_VETH; S_GONE0].

(* the 60 g_names entries with k % 16 <> 15 (index k + 2), then odd[1..4] (index 101..104) *)
Definition gtab : list (list byte * Z) :=
  map (fun k => (gname (Z.of_nat k), Z.of_nat k + 2))
      (filter (fun k => negb (Nat.eqb (Nat.modulo k 16) 15)) (seq 0 64)).
Definition link_tab : list (list byte * Z) :=
  gtab ++ [(S_ENP, 101); (S_ETH0, 102); (S_WLAN0, 103); (S_VETH, 104)].

(* name_of (fuzz_link.c:102-110), inlined in each arm: the selector byte s *)
Definition sel_name (s : Z) : option (list byte) :=
  if s =? 255 then None
  else if s <? 64 then Some (gname s)
  else Some (nth (Z.to_nat (s mod 6)) odd_strs []).
Definition sel_ptr (s : Z) : Z :=
  if s =? 255 then 0
  else if s <? 64 then A_G_NAMES + 8 * s
  else nth (Z.to_nat (s mod 6)) odd_ptrs 0.

(* ==========================================================================
   4. Memory views the loop keeps
   ========================================================================== *)

(* each 8-byte slot of g_names holds its name and a NUL, then bytes no one reads *)
Definition gnames_at (m : word -> option byte) : Prop :=
  forall k, 0 <= k < 64 -> exists rest,
    bytes_at rsegs m (A_G_NAMES + 8 * k) (gname k ++ zb 0 :: rest) /\
    length (gname k ++ zb 0 :: rest) = 8%nat.

(* the odd table and its strings (.data.rel.ro and .rodata: the image's bytes) *)
Definition odd_at (m : word -> option byte) : Prop :=
  forall i, (i < 6)%nat ->
    u64_at m (A_ODD + 8 * Z.of_nat i) (nth i odd_ptrs 0) /\ cstr_at m (nth i odd_ptrs 0) (nth i odd_strs []).

(* the input cursor: a suffix of the payload pl at p0 *)
Definition cursor_ok (m : word -> option byte) (p0 : Z) (pl : list byte) (P N : Z) : Prop :=
  bytes_at rsegs m p0 pl /\
  exists k, 0 <= k <= Z.of_nat (length pl) /\ P = p0 + k /\ N = Z.of_nat (length pl) - k.

(* a heap block of n bytes at a: outside the image's reserved segments and below the slot's stack *)
Definition blk_out (S a n : Z) : Prop :=
  4096 <= a /\ a + n <= S - SLOT_STACK_Z /\ pf_img_free a n.

(* tp holds the thread pointer the frame fixes (FrameAPI: ms_tp B = 0x75608), so errno is at
   0x75608 - 164 (link_mem ERRNO_TP_OFF); the stack protector's GOT slot and guard (snprintf's premises) *)
Definition A_TP : Z := 0x75608.
Definition A_ERRNO : Z := A_TP + ERRNO_TP_OFF.
Definition A_GOT_GUARD_S : Z := 0x208d8.
Definition A_GUARD_S : Z := 0x95878.
Definition guard_m (m : word -> option byte) : Prop :=
  bytes_at rsegs m A_GOT_GUARD_S (le8 (wz A_GUARD_S)) /\ exists c, bytes_at rsegs m A_GUARD_S (le8 c).

(* ==========================================================================
   5. The loop head
   ========================================================================== *)

(* What is fixed for one call of the slot: S (sp at entry), the model block md (8856 bytes), the
   marks block mk (516 bytes), the payload pl at p0, and the 104 saved bytes. *)
Record lenv : Type := LEnv {
  e_S : Z;
  e_md : Z;
  e_mk : Z;
  e_p0 : Z;
  e_pl : list byte;
  e_saved : list byte
}.

(* the placement of the slot's pieces: the stack window above the image, the two blocks and the
   payload outside the image and below the stack, and apart from each other *)
Definition lenv_ok (E : lenv) : Prop :=
  0x960e0 + SLOT_STACK_Z <= e_S E /\ e_S E <= 2 ^ 47 /\ e_S E mod 16 = 0 /\
  blk_out (e_S E) (e_md E) MD_SIZE /\ blk_out (e_S E) (e_mk E) MK_SIZE /\
  e_md E mod 16 = 0 /\ e_mk E mod 16 = 0 /\
  (e_md E + MD_SIZE <= e_mk E \/ e_mk E + MK_SIZE <= e_md E) /\
  1 <= Z.of_nat (length (e_pl E)) < 2 ^ 26 /\
  blk_out (e_S E) (e_p0 E) (Z.of_nat (length (e_pl E))) /\
  (e_p0 E + Z.of_nat (length (e_pl E)) <= e_md E \/ e_md E + MD_SIZE <= e_p0 E) /\
  (e_p0 E + Z.of_nat (length (e_pl E)) <= e_mk E \/ e_mk E + MK_SIZE <= e_p0 E) /\
  length (e_saved E) = 104%nat.

(* msg_build's static long_alias (0x743f8, 301 bytes, .bss): kernel writes its first 300 bytes and reads it
   with strlen, so it asks the NUL at [300] and the 3 slack bytes after it (kernel_c.v Pre). The NUL lives
   across driver calls in the slot's GI (LLVMFuzzerTestOneInput_c.v llvm_GI). *)
Definition la_ok (m : word -> option byte) : Prop :=
  exists la sl, rw_cells rsegs m A_LONG_ALIAS [CB (Z.to_nat 300) la; C1 (zb 0)] /\
    bytes_at rsegs m (A_LONG_ALIAS + LONG_ALIAS_SIZE) sl /\ length sl = 3%nat.

(* texts[] (0x207f0, 11 pointers in .data.rel.ro, read from the image) and where interfaces() points
   g_nl.if_name[i]: g_names + 8 k for the 60 kept k, then odd[1..4] (0x138ec-0x13984). Both regions are
   carried: no operation writes .data.rel.ro, and NK_IF_NAME (271024) lies above every callee's g_nl writes. *)
Definition texts_ptrs : list Z :=
  [0x10368; 0x10341; 0x10488; 0x102a8; 0x10517; 0x10429; 0x10520; 0x1056f; 0x10329; 0x10497; 0x10554].
Definition texts_at (m : word -> option byte) : Prop :=
  forall i, (i < 11)%nat -> u64_at m (A_TEXTS + 8 * Z.of_nat i) (nth i texts_ptrs 0).
Definition link_ptrs : list Z :=
  map (fun k => A_G_NAMES + 8 * Z.of_nat k) (filter (fun k => negb (Nat.eqb (Nat.modulo k 16) 15)) (seq 0 64))
  ++ [0x1039c; 0x1056a; 0x103bc; 0x10598].
Definition ifptrs_at (m : word -> option byte) : Prop :=
  forall i, (i < 64)%nat -> u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) (nth i link_ptrs 0).

(* the memory at the loop head of operation i (0 <= i <= 47), with the fake kernel kbs, the model mbs,
   the marks gbs and the cursor (P, N) *)
Definition lh_mem (E : lenv) (i P N : Z) (kbs mbs gbs : list byte) (m : word -> option byte) : Prop :=
  (exists j0 j1 j2 nc, rw_cells rsegs m (e_S E - SLOT_FRAME) (lh_cells (e_md E) (e_mk E) P nc j0 j1 j2)) /\
  bytes_at rsegs m (e_S E - 104) (e_saved E) /\
  nlk_at m kbs /\ nlk_wf kbs /\ iftab_at m kbs link_tab /\
  nk_open kbs = 0 /\ nk_misuse kbs = 0 /\ nk_opened kbs = nk_closed kbs /\ nk_opened kbs <= 64 * i /\
  gnames_at m /\ odd_at m /\ policy_ro m /\
  la_ok m /\ texts_at m /\ ifptrs_at m /\
  model_at m (e_md E) mbs /\ model_wf mbs /\
  marks_at m (e_mk E) gbs /\ marks_wf gbs /\ marks_are gbs mbs /\
  cursor_ok m (e_p0 E) (e_pl E) P N /\
  wr_at rsegs m A_ERRNO 4 /\ guard_m m.

(* the machine state at the loop head *)
Definition lh_ms (E : lenv) (i : Z) (gp : word) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (P N : Z) (kbs mbs gbs : list byte),
    ms = MS (mkR ra (wz (e_S E - SLOT_FRAME)) gp (wz A_TP) t0 t1 t2 (wz (e_md E)) (wz GNL40) a0 a1 a2 a3 a4 a5 a6 a7
                 (wz N) s3 s4 (wz 46) (wz A_JT) (wz (e_mk E)) (wz 0xab) (wz 4) (wz (e_md E + MD_N_REQ)) (wz i)
                 t3 t4 t5 t6)
            F (wz L_LH) fc None m (seg_rom rsegs) /\
    frm0 fc /\ 0 <= i <= 47 /\ 1 <= N /\
    lh_mem E i P N kbs mbs gbs m /\
    mem_inv rsegs m /\ MemNorm.task_mem rsegs m /\
    stk rsegs m (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME).

(* the machine state at L_EXIT (0x1413c: mv a0, s7; jal free; mv a0, s0; jal free; return 0), reached from
   the loop's tails (after operation 47, or when the input is used up) and from 0x139b4 when size = 0:
   s0 = md, s7 = mk, the frame and the saved bytes in place *)
Definition ex_ms (E : lenv) (gp : word) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (j : list byte),
    ms = MS (mkR ra (wz (e_S E - SLOT_FRAME)) gp (wz A_TP) t0 t1 t2 (wz (e_md E)) s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 (wz (e_mk E)) s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz L_EXIT) fc None m (seg_rom rsegs) /\
    frm0 fc /\
    rw_cells rsegs m (e_S E - SLOT_FRAME) [CB 376 j] /\
    bytes_at rsegs m (e_S E - 104) (e_saved E) /\
    wr_at rsegs m A_ERRNO 4 /\ guard_m m /\ la_ok m /\
    mem_inv rsegs m /\ MemNorm.task_mem rsegs m /\
    stk rsegs m (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME).

(* A segment that passes a leaf call ends in a state the leaf contract gives only up to its register file
   (regs' with regs_preserved); RegisterBridge.canonical_contract_transport moves the walk to the canonical
   mkR form, so a segment's post is stated up to ms_eqv: `eqv_cl P ms'`. The SR glue reads P of the canonical
   state (for P in mkR form the canonical state of an eqv-related state satisfies P). *)
Definition eqv_cl (P : machine_state -> Prop) (ms : machine_state) : Prop :=
  exists c, P c /\ Regs6ss.ms_eqv c ms.

(* the operation the loop head of ms dispatches: the byte at the cursor P that the frame cell sp+0x40
   holds, mod 6 (0x13a1c-0x13a64). Every arm starts from `lh_ms E i gp ms /\ lh_op E ms k` (a Theorem Labs lane's text). *)
Definition lh_op (E : lenv) (ms : machine_state) (op : Z) : Prop :=
  exists P b, bytes_at rsegs (ms_mem ms) (e_S E - SLOT_FRAME + FO_P) (le8 (wz P)) /\
    bytes_at rsegs (ms_mem ms) P [b] /\ bz b mod 6 = op.

(* What one segment of the slot's own code (leaf calls included) may write: its stack window, g_nl,
   g_names, long_alias, errno and the heap blocks hp it holds; never the FILE block, never g_sink / g_say /
   g_said / ofl_head (only mark_quietly, an SR call, writes those). Every segment's post carries
   `seg_fp (e_S E) hp m0 m'` against its start memory m0, so the SR frame survives it (a Theorem Labs lane's text). *)
Definition own_w (S : Z) (hp : list (Z * Z)) (x : Z) : Prop :=
  (S - SLOT_STACK_Z <= x < S) \/ (A_G_NL <= x < A_G_NL + NK_SIZE) \/
  (A_G_NAMES <= x < A_G_NAMES + G_NAMES_SIZE) \/
  (A_LONG_ALIAS <= x < A_LONG_ALIAS + LONG_ALIAS_SIZE) \/ (A_ERRNO <= x < A_ERRNO + 4) \/
  (exists a k, In (a, k) hp /\ a <= x < a + k).
Definition seg_fp (S : Z) (hp : list (Z * Z)) (m m' : word -> option byte) : Prop :=
  exists W, munch W m m' /\ wmono rsegs m m' /\ (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x -> own_w S hp x).
