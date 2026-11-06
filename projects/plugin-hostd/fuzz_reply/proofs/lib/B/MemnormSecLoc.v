(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/MemnormSecLoc.v (commit 30a1993588f, c5 + memnorm; file sha256 8ae4fc6e3a4e) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 2 image addresses moved by code-verified function pairs (4 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py); no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/MemnormSecLoc.v at commit 789778cb16f, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan (2 numerals; per-numeral report). *)
(* Theorem Labs, 2026-10 (task MEMNORM, full Allocate): the two cgif_file location lemmas the secondary Allocate arms'
   memnorm twins need (measurement secondary-frames.md (sha256 05a349cba232; internal record)).
   rule 24: no function proved (kind: image / location lemmas).

   Each arm of AGk0.sec_arms_w ends in an arm-level raw frame relative to Allocate's entry memory, and every zone of it
   is mn_safe (not read-only, below TASK_SIZE), so MemnormT.memnorm_frame gives the keep:
   - [memnorm_winpn]: the refusal arm's frame (at_RETS's MEQ over AGjn.WINPN = AGjm.WINP, the OOM byte and errno;
     AGk0.refuseS, AGk0.v:355-390): the stack window (MemnormHitG.mn_safe_high), the thread-object cells AGjm.WINT
     (MemnormHitG.mn_safe_owned), the instance cells AGjm.WINI (RW statics: AGk0's Hinst, AGk0.v:184, and
     AGjm.BSLv_range, AGjm.v:374: INSTv + 296 <= BSLv <= INSTv + 400 at c5 84ee52cd012), the OOM byte and errno (MemnormSafecgif.mn_safe_rw);
   - [memnorm_sfin_win]: the grant arms' frame (AGif4.sfin's sf_MEQF, AGif4.v:88-90, over AGjm.WIN, AGif4.QRz on grow
     and AGif4.DXz; the premise shape of AGif5.frame_grant_raw, AGif5.v:977-979): besides the above, the pointer-array
     slot and the next commit (inside the owned extent (ly_Q, kPtrArrayResv), YG0f.v:296-299), the new map (a zone3
     extent below ASAN_CEIL, MemnormLoc.mn_safe_zone3), its shadow (at or above kImgEnd), the depot's stack window and
     the depot zone AGjm.DZONE (RW static, NB and SB blocks).
   AGk0, AGif4, AGif5 and every existing statement are unchanged. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YF0m YF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require AGhy AGjm AGjn AGif4 ImgBaseAGS.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AGif2reply AGif4reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require MemnormT MemnormHitG MemnormSafereply MemnormLocG MemnormLoc.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YAkMemnorm.
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* The refusal arm's window: AGjm.WINP (stack window, thread-object cells, instance cells), the OOM byte and errno. *)
Lemma memnorm_winpn : forall ly (regs0 : bvmap 5 word) (n : Z) (mem0 m : word -> option byte),
  layout_ok ly -> img_cover ly ->
  ly_stk_lo ly + AGhy.AFSTACK <= bv_unsigned (getr regs0 2) -> bv_unsigned (getr regs0 2) <= ly_stk_hi ly ->
  0x9d000 <= bv_unsigned (getr regs0 11) -> bv_unsigned (getr regs0 11) + 0xe60 <= 0x1288a0 ->
  bv_unsigned (getr regs0 11) + 296 <= AGjm.BSLv regs0 n <= bv_unsigned (getr regs0 11) + 400 ->
  (forall x : word, ~ AGjn.WINPN ly regs0 n (bv_unsigned x) -> m x = mem0 x) -> MemnormT.memnorm_keep tfibsegs mem0 m.
Proof.
intros ly regs0 n mem0 m LY IMG Hlo Hhi I1 I2 HB F.
pose proof (lo_top ly LY) as (_ & _ & _ & T4 & _ & _ & T7).
apply (MemnormLocG.memnorm_keep_window tfibsegs (AGjn.WINPN ly regs0 n) mem0 m); [|exact F].
intros x Hw. unfold AGjn.WINPN, AGjm.WINP in Hw. cbv zeta in Hw. destruct Hw as [[Hw|[Hw|Hw]]|[Hw|Hw]].
- apply MemnormHitG.mn_safe_high. unfold AGhy.AFSTACK, ImgBaseAGS.AFSTACK, kHighMemBeg, kHighMemEnd, kImgEnd, TASK_SIZE in *. lia.
- apply (MemnormHitG.mn_safe_owned ly (ly_T ly, kThreadObjSize) x LY IMG
    ltac:(unfold owned_extents; right; right; left; reflexivity)).
  cbn [fst snd]. unfold AGjm.WINT in Hw. cbv zeta in Hw. unfold t_unwinding, kThreadObjSize in *. lia.
- apply MemnormSafereply.mn_safe_rw. unfold AGjm.WINI in Hw. cbv zeta in Hw.
  unfold o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, o_comb_stats, TASK_SIZE in *. lia.
- apply MemnormSafereply.mn_safe_rw. unfold TFIB_OOM, TASK_SIZE in *. lia.
- apply MemnormSafereply.mn_safe_rw. unfold TFIB_ERRNO, TASK_SIZE in *. lia.
Qed.

(* The grant arms' window: AGjm.WIN, the next pointer-array commit on grow (AGif4.QRz) and the depot's zone
   (AGif4.DXz). *)
Lemma memnorm_sfin_win : forall ly (regs0 : bvmap 5 word) (n idx res mb : Z) (grow : bool) (mem0 m : word -> option byte),
  layout_ok ly -> img_cover ly ->
  ly_stk_lo ly + AGhy.AFSTACK <= bv_unsigned (getr regs0 2) -> bv_unsigned (getr regs0 2) <= ly_stk_hi ly ->
  0x9d000 <= bv_unsigned (getr regs0 11) -> bv_unsigned (getr regs0 11) + 0xe60 <= 0x1288a0 ->
  bv_unsigned (getr regs0 11) + 296 <= AGjm.BSLv regs0 n <= bv_unsigned (getr regs0 11) + 400 ->
  0 <= idx < kMaxNumChunks -> 0 <= res -> 0 <= AGjm.MSv n -> zone3 mb (AGjm.MSv n) ->
  (forall x : word, ~ AGjm.WIN ly regs0 n idx mb (bv_unsigned x) -> ~ (grow = true /\ AGif4.QRz ly res (bv_unsigned x)) ->
    ~ AGif4.DXz ly (bv_unsigned (getr regs0 2)) (bv_unsigned x) -> m x = mem0 x) ->
  MemnormT.memnorm_keep tfibsegs mem0 m.
Proof.
intros ly regs0 n idx res mb grow mem0 m LY IMG Hlo Hhi I1 I2 HB Hidx Hres MS0 HZ F.
pose proof (lo_top ly LY) as (_ & _ & _ & T4 & _ & _ & T7).
pose proof HZ as HZ'. unfold zone3 in HZ'. destruct HZ' as (M0 & M2 & _).
pose proof (ASAN_CEIL_range) as [CR CR2].
assert (D1 : 0 <= mb / 8 /\ 8 * (mb / 8) <= mb) by (split; [apply Z.div_pos | apply Z.mul_div_le]; lia).
assert (D2 : 0 <= AGjm.MSv n / 8 /\ 8 * (AGjm.MSv n / 8) <= AGjm.MSv n) by (split; [apply Z.div_pos | apply Z.mul_div_le]; lia).
apply (MemnormT.memnorm_frame tfibsegs (fun a => AGjm.WIN ly regs0 n idx mb a \/ (grow = true /\ AGif4.QRz ly res a) \/
  AGif4.DXz ly (bv_unsigned (getr regs0 2)) a) mem0 m).
- intros x [Hw|[[_ Hq]|Hd]].
  + unfold AGjm.WIN in Hw. cbv zeta in Hw. destruct Hw as [Hw|[Hw|[Hw|Hw]]].
    * apply MemnormHitG.mn_safe_high. unfold AGhy.AFSTACK, ImgBaseAGS.AFSTACK, kHighMemBeg, kHighMemEnd, kImgEnd, TASK_SIZE in *. lia.
    * apply (MemnormHitG.mn_safe_owned ly (ly_T ly, kThreadObjSize) x LY IMG
        ltac:(unfold owned_extents; right; right; left; reflexivity)).
      cbn [fst snd]. unfold AGjm.WINT in Hw. cbv zeta in Hw. unfold t_unwinding, kThreadObjSize in *. lia.
    * apply MemnormSafereply.mn_safe_rw. unfold AGjm.WINI in Hw. cbv zeta in Hw.
      unfold o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, o_comb_stats, TASK_SIZE in *. lia.
    * unfold AGjm.WINM in Hw. cbv zeta in Hw. destruct Hw as [Hw|[Hw|Hw]].
      -- apply (MemnormHitG.mn_safe_owned ly (ly_Q ly, kPtrArrayResv) x LY IMG
           ltac:(unfold owned_extents; right; left; reflexivity)).
         cbn [fst snd]. unfold AGjm.QSv in Hw. cbv zeta in Hw. unfold kPtrArrayResv, kMaxNumChunks in *. lia.
      -- exact (MemnormLoc.mn_safe_zone3 mb (AGjm.MSv n) x HZ Hw M2).
      -- apply MemnormHitG.mn_safe_high. unfold AGjm.SMv, AGjm.SHBv in Hw.
         unfold kImgEnd, TASK_SIZE in *. lia.
  + apply (MemnormHitG.mn_safe_owned ly (ly_Q ly, kPtrArrayResv) x LY IMG
      ltac:(unfold owned_extents; right; left; reflexivity)).
    cbn [fst snd]. unfold AGif4.QRz in Hq. unfold kPtrArrayEntriesPerCommit, kPtrArrayResv in *. lia.
  + unfold AGif4.DXz in Hd. destruct Hd as [Hs|Hz].
    * apply MemnormHitG.mn_safe_high.
      unfold ImgBaseAGS.DEP_STK, AGhy.AFSTACK, ImgBaseAGS.AFSTACK, kHighMemBeg, kHighMemEnd, kImgEnd, TASK_SIZE in *. lia.
    * change (AGjm.DZONE ly (bv_unsigned x)) in Hz. unfold AGjm.DZONE in Hz. destruct Hz as [Hz|[Hz|Hz]].
      -- apply MemnormSafereply.mn_safe_rw. unfold TASK_SIZE. lia.
      -- apply (MemnormHitG.mn_safe_owned ly (ly_NB ly, kNodesBlockSize) x LY IMG
           ltac:(unfold owned_extents; right; right; right; right; left; reflexivity)). exact Hz.
      -- apply (MemnormHitG.mn_safe_owned ly (ly_SB ly, kStoreBlockSize) x LY IMG
           ltac:(unfold owned_extents; right; right; right; right; right; left; reflexivity)). exact Hz.
- intros x N. apply F; intros X; apply N; [left | right; left | right; right]; exact X.
Qed.
End a.
