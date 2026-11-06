(* reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3): the part of the
   harness walk's instantiation that lib/B/Prog/SegInstB.v (this walk's instantiation lane, image B's copy of
   the image-A owner's SegInstA names) does not state: the room the harness's own window leaves its callees. The image-B
   twin of lib/A/Prog/LLVMFuzzerTestOneInput_inst.v (image A's cut-statement commit 6888a1bad128). Statement text
   only: no function of the binary is proved here.

   Every number of the walk comes from SegInstB (STK_LLVMFuzzerTestOneInput and the callees' STK_<F>, emptyA,
   RLO_A, RHI_A, longlA, mod40A, catA, wordsA, rolesA, gotwA, guardA, memchr_loA, memchr_hiA, seg_litA_fz,
   seg_litA_rc: SegInstA's names at image B's values), and, by the image-A owner's ruling of 2026-10-30, the walk names
   a function entry as BASE + AF_<F> and a runtime target as pa_sigma SS_<x> (listing terms under
   `Context {PI : PAImg seg_listing}`), never SegInstB's concrete A_<F>_A / pc_<x>A, which are the close's.

   WHY THESE LEMMAS: the harness's realigned frame is at most 352 + 16 bytes below the entry sp (`addi
   sp,sp,-352` at 0x84dc0 and `andi sp,sp,-32` at 0x84e00, dis/LLVMFuzzerTestOneInput.fuzz_segconf.asan-ubsan.s
   (sha256 be3c0d79cc92) lines 2 and 18, from a 16-aligned entry sp, afn_pre's astk_ok); every call runs at
   sp = S1, and the deepest window a call there asks is the allocator wrappers' ASTACK (amalloc04_rule /
   afree04_rule: ASTACK - o <= STK with o = S1 - SP0, lib/B/YC5d.v:64, :83); every one of the 22 callees' windows
   is at most ASTACK. So each call of the walk finds its callee's window inside [SP0 - STK_LLVMFuzzerTestOneInput,
   S1). The callees are image A's 22 (map PLAN-asanubsan-main section 8 item 1, out/callee_sets.txt sha256
   9a1cc897a906: the same callee set; strip and fold, image B's two extra functions, are called by m_file only). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegInstB.
Import ListNotations.
Local Open Scope Z_scope.

(* the harness's realigned frame below the entry sp *)
Definition LTOI_FRAME_MAX : Z := 352 + 16.
Lemma ltoi_stk_room : LTOI_FRAME_MAX + ASTACK <= STK_LLVMFuzzerTestOneInput.
Proof. vm_compute. discriminate. Qed.
(* the windows of the harness's 22 callees (PLAN-asanubsan-main section 5), each at most ASTACK *)
Definition LTOI_CALLEE_STKS : list Z :=
  [STK_reac_segconf_init; STK_m_file; STK_reac_segconf_parse_file; STK_m_refuse; STK_reac_segconf_parse;
   STK_check_segments; STK_reac_segconf_role; STK_check_role; STK_reac_segconf_model; STK_check_model;
   STK_reac_segconf_ignored; STK_check_ignore; STK_reac_segconf_role_file; STK_reac_segconf_ignore_file;
   STK_check_provenance; STK_check_refusals; STK_check_address; STK_check_knock_refused; STK_m_find;
   STK_check_absent; STK_reac_segconf_declared; STK_check_declared].
Lemma ltoi_callee_stks_b : forallb (fun k => (0 <=? k) && (k <=? ASTACK)) LTOI_CALLEE_STKS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ltoi_callee_stks : forall k, In k LTOI_CALLEE_STKS -> 0 <= k /\ LTOI_FRAME_MAX + k <= STK_LLVMFuzzerTestOneInput.
Proof.
intros k Hk. pose proof (proj1 (forallb_forall _ _) ltoi_callee_stks_b k Hk) as H. cbn beta in H.
apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
pose proof ltoi_stk_room as R. lia.
Qed.
