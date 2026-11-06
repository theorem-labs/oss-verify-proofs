(* The slot LLVMFuzzerTestOneInput, plain image: the cut predicates of the op_write arm
   (fuzz_link.c:735-751, operation byte % 6 = 1, jump-table target 0x13bcc).

   The arm runs in three evt segments, cut at its two allocator-facing calls:
     A  lh_ms (0x13a1c) -> the call of text_of (0x13fb4, entry 0x15aa8, ra 0x13fb8):
        the dispatch 0x13a1c-0x13a64 and the inlined name_of 0x13bcc-0x13d18 / 0x13f80-0x13fa8.
     B  text_of's return (0x13fb8) -> the call of free(own) (0x1405c, entry 0x173d4, ra 0x14060):
        kernel, model_begin, model_write, reac_link_alias_write, check_socket, the refusal test
        (strlen, index_of, check_refused), check_write, check_requests.
     C  free's return (0x14060) -> lh_ms of the next operation (0x13a1c) or ex_ms (0x1413c).
   Each cut predicate is stated as LDefs.lh_ms is: the whole register file as `mkR`, frm0, the loop
   memory lh_mem, mem_inv, task_mem and the stack window; memory facts only over the regions the SR
   glue carries (SLOT-COMMON.md). Every address below is read from the plain image (the unstripped
   twin of the pin ebe34b259b9f; link/ct/dis/plain/LLVMFuzzerTestOneInput.s). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Program points of the arm (plain)
   ========================================================================== *)

Definition C1_TEXT_OF : Z := 0x15aa8.     (* jal text_of at 0x13fb4 *)
Definition C1_TEXT_OF_RA : Z := 0x13fb8.
Definition C1_MW_RA : Z := 0x13ff8.        (* jal model_write at 0x13ff4 *)
Definition C1_FREE : Z := 0x173d4.         (* jal free at 0x1405c *)
Definition C1_FREE_RA : Z := 0x14060.

(* the heap blocks the arm's segments may write (LDefs.seg_fp): the model and the marks block. No
   segment of the arm writes text_of's block (text_of and free are SR cuts, not segment code). *)
Definition c1_hp (E : lenv) : list (Z * Z) := [(e_md E, MD_SIZE); (e_mk E, MK_SIZE)].

(* ==========================================================================
   2. The alias: text_of's answer
   ========================================================================== *)

(* text_of's answer s (kept in s5 from 0x13fb8): the C string t, then the bytes strlen reads after
   its NUL up to the next multiple of 8 (strlen_c.v; model_write_c.v and reac_link_alias_write_c.v
   ask the same of the alias), the whole run [s, s + |t| + 1 + |sl|) apart from every region the
   segment B writes: the stack window (the slot's frame and its callees' frames), g_nl,
   long_alias with its 3 slack bytes, the model block and errno. *)
Definition al_ok (E : lenv) (m : word -> option byte) (s : Z) (t sl : list byte) : Prop :=
  s <> 0 /\
  bytes_at rsegs m s (t ++ zb 0 :: sl) /\ ~ In (zb 0) t /\ Z.of_nat (length t) < 320 /\
  Z.of_nat (length sl) = (- (s + Z.of_nat (length t) + 1)) mod 8 /\
  apart s (Z.of_nat (length t) + 1 + Z.of_nat (length sl)) (e_S E - SLOT_STACK_Z) SLOT_STACK_Z /\
  apart_gnl s (Z.of_nat (length t) + 1 + Z.of_nat (length sl)) /\
  apart s (Z.of_nat (length t) + 1 + Z.of_nat (length sl)) A_LONG_ALIAS 304 /\
  apart s (Z.of_nat (length t) + 1 + Z.of_nat (length sl)) (e_md E) MD_SIZE /\
  apart s (Z.of_nat (length t) + 1 + Z.of_nat (length sl)) A_ERRNO 4.

(* ==========================================================================
   3. The cuts
   ========================================================================== *)

(* (cut 1) the call of text_of(&in, &own) at 0x13fb4: pc = 0x15aa8, ra = 0x13fb8, a0 = sp + 0x40 (the
   cursor), a1 = sp + 0x78 (own), s2 = name_of's answer for the selector byte nb (0 when the op byte
   was the last input byte). The cursor (P, N) has moved past the op byte and the selector byte and
   is in the frame cells sp + 0x40 / sp + 0x48. text_of's Pre over the slot's facts: the two cursor
   cells, the own cell (any word: the 256-byte buffer at sp + 0x78), the input bytes (cursor_ok). *)
Definition c1_15aa8 (E : lenv) (i : Z) (gp : word) (ms : machine_state) : Prop :=
  exists (t0 t1 t2 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (P N : Z) (kbs mbs gbs : list byte) (nb : Z),
    ms = MS (mkR (wz C1_TEXT_OF_RA) (wz (e_S E - SLOT_FRAME)) gp (wz A_TP) t0 t1 t2 (wz (e_md E)) (wz GNL40)
                 (wz (e_S E - SLOT_FRAME + FO_P)) (wz (e_S E - SLOT_FRAME + FO_B256)) a2 a3 a4 a5 a6 a7
                 (wz (sel_ptr nb)) s3 s4 (wz 46) (wz A_JT) (wz (e_mk E)) (wz 0xab) (wz 4)
                 (wz (e_md E + MD_N_REQ)) (wz i) t3 t4 t5 t6)
            F (wz C1_TEXT_OF) fc None m (seg_rom rsegs) /\
    frm0 fc /\ 0 <= i <= 47 /\ 0 <= nb < 256 /\ 0 <= N /\
    lh_mem E i P N kbs mbs gbs m /\
    rw_cells rsegs m (e_S E - SLOT_FRAME + FO_P) [C8 (wz P); C8 (wz N)] /\
    mem_inv rsegs m /\ MemNorm.task_mem rsegs m /\
    stk rsegs m (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME).

(* (cut 2) text_of's return at 0x13fb8, with its Post (text_of_c.v) in the slot's terms: a0 = s, the
   answer; the own cell sp + 0x78 holds own, which is 0 (a `texts` entry) or s (the fresh block); the
   cursor moved on inside the payload; the callee-saved registers as at cut 1. `own` is a parameter:
   segment B passes it unchanged to cut 3, where free(own) is called. *)
Definition c1_13fb8 (E : lenv) (i : Z) (gp : word) (own : Z) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (P N : Z) (kbs mbs gbs : list byte) (nb s : Z) (t sl : list byte),
    ms = MS (mkR ra (wz (e_S E - SLOT_FRAME)) gp (wz A_TP) t0 t1 t2 (wz (e_md E)) (wz GNL40)
                 (wz s) a1 a2 a3 a4 a5 a6 a7
                 (wz (sel_ptr nb)) s3 s4 (wz 46) (wz A_JT) (wz (e_mk E)) (wz 0xab) (wz 4)
                 (wz (e_md E + MD_N_REQ)) (wz i) t3 t4 t5 t6)
            F (wz C1_TEXT_OF_RA) fc None m (seg_rom rsegs) /\
    frm0 fc /\ 0 <= i <= 47 /\ 0 <= nb < 256 /\ 0 <= N /\
    lh_mem E i P N kbs mbs gbs m /\
    rw_cells rsegs m (e_S E - SLOT_FRAME + FO_P) [C8 (wz P); C8 (wz N)] /\
    bytes_at rsegs m (e_S E - SLOT_FRAME + FO_B256) (le8 (wz own)) /\
    (own = 0 \/ own = s) /\
    al_ok E m s t sl /\
    mem_inv rsegs m /\ MemNorm.task_mem rsegs m /\
    stk rsegs m (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME).

(* (inside segment B, not an SR cut) model_write's return at 0x13ff8, after kernel and model_begin:
   a0 = the model's answer w_rc WM, s4 = g_nl.opened read at 0x13fdc, s5 = the alias s; the fake
   kernel kbs is the one kernel left with n_sent = 0 (0x13fe4), so nk_sent kbs = [] and the model's
   kstate is nk_kstate kbs; the model block mbs holds WM's requests. *)
Definition c1_wm (nb : Z) (t : list byte) (kbs : list byte) : wres :=
  write_model link_tab (sel_name nb) (Some t) [] (nk_kstate kbs).

Definition c1_13ff8 (E : lenv) (i : Z) (gp : word) (own : Z) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (P N : Z) (kbs mbs gbs : list byte) (nb s : Z) (t sl : list byte),
    ms = MS (mkR ra (wz (e_S E - SLOT_FRAME)) gp (wz A_TP) t0 t1 t2 (wz (e_md E)) (wz GNL40)
                 (wz (w_rc (c1_wm nb t kbs))) a1 a2 a3 a4 a5 a6 a7
                 (wz (sel_ptr nb)) s3 (wz (nk_opened kbs)) (wz s) (wz A_JT) (wz (e_mk E)) (wz 0xab) (wz 4)
                 (wz (e_md E + MD_N_REQ)) (wz i) t3 t4 t5 t6)
            F (wz C1_MW_RA) fc None m (seg_rom rsegs) /\
    frm0 fc /\ 0 <= i <= 47 /\ 0 <= nb < 256 /\ 0 <= N /\
    lh_mem E i P N kbs mbs gbs m /\
    nk_n_sent kbs = 0 /\
    md_reqs mbs = w_reqs (c1_wm nb t kbs) /\
    md_n_req mbs = Z.of_nat (length (w_reqs (c1_wm nb t kbs))) /\
    rw_cells rsegs m (e_S E - SLOT_FRAME + FO_P) [C8 (wz P); C8 (wz N)] /\
    bytes_at rsegs m (e_S E - SLOT_FRAME + FO_B256) (le8 (wz own)) /\
    (own = 0 \/ own = s) /\
    al_ok E m s t sl /\
    mem_inv rsegs m /\ MemNorm.task_mem rsegs m /\
    stk rsegs m (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME).

(* (cut 3) the call of free(own) at 0x1405c: pc = 0x173d4, ra = 0x14060, a0 = own (loaded from
   sp + 0x78 at 0x14058). The checks have passed; the loop memory holds for operation i + 1 (the
   alias writer may have opened one socket: g_nl.opened <= 64 i + 1). *)
Definition c1_173d4 (E : lenv) (i : Z) (gp : word) (own : Z) (ms : machine_state) : Prop :=
  exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (P N : Z) (kbs mbs gbs : list byte),
    ms = MS (mkR (wz C1_FREE_RA) (wz (e_S E - SLOT_FRAME)) gp (wz A_TP) t0 t1 t2 (wz (e_md E)) (wz GNL40)
                 (wz own) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 (wz (e_mk E)) (wz 0xab) (wz 4)
                 (wz (e_md E + MD_N_REQ)) (wz i) t3 t4 t5 t6)
            F (wz C1_FREE) fc None m (seg_rom rsegs) /\
    frm0 fc /\ 0 <= i <= 47 /\ 0 <= N /\
    lh_mem E (i + 1) P N kbs mbs gbs m /\
    rw_cells rsegs m (e_S E - SLOT_FRAME + FO_P) [C8 (wz P); C8 (wz N)] /\
    mem_inv rsegs m /\ MemNorm.task_mem rsegs m /\
    stk rsegs m (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME).

(* (cut 4) free's return at 0x14060: the callee-saved registers the tail reads (s0, s1, s7 - s11, sp,
   gp, tp) as at cut 3, the rest any word. *)
Definition c1_14060 (E : lenv) (i : Z) (gp : word) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 t3 t4 t5 t6 : word) (F : bvmap 5 word)
         (fc : bv 32) (m : word -> option byte) (P N : Z) (kbs mbs gbs : list byte),
    ms = MS (mkR ra (wz (e_S E - SLOT_FRAME)) gp (wz A_TP) t0 t1 t2 (wz (e_md E)) (wz GNL40)
                 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 (wz (e_mk E)) (wz 0xab) (wz 4)
                 (wz (e_md E + MD_N_REQ)) (wz i) t3 t4 t5 t6)
            F (wz C1_FREE_RA) fc None m (seg_rom rsegs) /\
    frm0 fc /\ 0 <= i <= 47 /\ 0 <= N /\
    lh_mem E (i + 1) P N kbs mbs gbs m /\
    rw_cells rsegs m (e_S E - SLOT_FRAME + FO_P) [C8 (wz P); C8 (wz N)] /\
    mem_inv rsegs m /\ MemNorm.task_mem rsegs m /\
    stk rsegs m (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME).

(* the post of segment C: the next loop head, or the exit *)
Definition c1_next (E : lenv) (i : Z) (gp : word) (ms : machine_state) : Prop :=
  (i < 47 /\ lh_ms E (i + 1) gp ms) \/ ex_ms E gp ms.
