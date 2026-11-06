(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/A/HPgSatSeg.v at dd9ff534326, the image-B twin
   (fuzz_headamp.asan-ubsan): image B's segments read from lib/AU/Img0U.v; the statement hd_seg_static and the
   image-free helpers (rng_apartb, all_apartb, ranges_chk, cut_cells, cut_regs and their lemmas) are HPgSatSeg.v's,
   used by name; the three checkers HPgSatSeg.v states over image A's segments (strs_chk, at_chk, cut_chk) are
   restated over a segment list; the 43 descriptors, the shadow spans and the guard are lib/AU/HPgSatU.v's; the run's
   quantities are chosen at image B's real frame (R = (S - 0x220) & -32); the record is lib/AU/HPgImgB.v's, whose
   cut lists hold image B's own registers and real-frame cells (among them 1 - the null flag at R+0x38). *)
(* Image B's witness for the image-level premises of reac-pw/fuzz_headamp's five segment contracts (lib/A/HPgCSpec.v:
   the image-level conjuncts of hd_seg_pre, the cut lists hi_L1 .. hi_L9, and what headamp_build_contract ..
   headamp_plain_contract ask of the run's quantities alone) at I = headamp_himg_B (lib/AU/HPgImgB.v). At one
   concrete state over image B's loaded segments, the frame's shadow bytes, the 43 registered globals, the checked
   real-frame range, the 36 strings, the read-only cells, the read-only data, the stack-guard cells, the read-only
   segments and the live values at all nine cuts hold together, so those premises are not vacuous on image B; the
   same state with the res granules in scope gives them at hi_shB. Each shadow byte the witness memory holds is the
   one the runtime writes, and each program byte is read from the image.
   Pinned image: fuzz_headamp.asan-ubsan, sha256 53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94.
   proves no function (kind: statement text) *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YP09 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YO0f YG00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require HPgSat HPgSatSeg.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgImgB Img0U HPgSatU.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ======================================== the registered globals ======================================== *)
(* The 43 rows of HPgSatU.headamp_B_globals (each the image's descriptor, HPgSatU.headamp_B_globals_chk; the table
   the runtime registers, HPgSatU.headamp_B_reg_chk; the rows of hi_globs, HPgSatU.headamp_B_globals_globs): their
   ranges [beg, beg + size_with_redzone) are ascending and apart (so each granule has at most one global's shadow
   byte) and lie in HPgSatU.shadow_spans_B; each string of hi_strs is in the image with its NUL and is the global
   with beg = its address and size = its length + 1 (cstrs_img_chk). *)
Lemma headamp_B_globals_apart_chk :
  forallb (fun k => let '(_, (b1, _, r1)) := nth k headamp_B_globals HPgSat.gdummy in
                    let '(_, (b2, _, _)) := nth (S k) headamp_B_globals HPgSat.gdummy in b1 + r1 <=? b2) (seq 0 42) &&
  forallb (fun g => let '(_, (b, _, r)) := g in existsb (fun s => (fst s <=? b) && (b + r <=? snd s)) shadow_spans_B)
    headamp_B_globals &&
  HPgSat.cstrs_img_chk Img0U.rsegs headamp_B_globals (hi_strs headamp_himg_B) = true.
Proof. vm_compute. reflexivity. Qed.

(* ======================================== the run's quantities ======================================== *)
(* S the entry sp (a user stack address); R = (S - 0x220) & -32 (the prologue's s1, HPgImgB.v's header, pinned image
   sha256 53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94); F a class-4 side-stack frame for
   locals (1024-byte frames, 1024-aligned); the four blocks the harness allocates, each 16-aligned as the allocator
   returns them: pp (19744 bytes), pod (len), out (3 cap + 3) and first (3 max(rc, 0), or 1 when that is 0); the
   input after the two harness bytes at src (left bytes). len = 16, cap = 3, the null flag 0 and the parse's answer
   rc = 2 are chosen in the ranges the contracts ask (0 <= cap <= 9, 0 <= null <= 1, -1 <= rc <= cap); no conjunct
   below ties len or rc to an input. *)
Definition env_segB : hd_env := {|
  e_S := 0x7fffffff0000; e_R := 0x7ffffffefde0; e_F := 0x7ff000000000;
  e_pp := 0x7e0000000010; e_pod := 0x7e0000010010; e_out := 0x7e0000020010; e_first := 0x7e0000030010;
  e_len := 16; e_cap := 3; e_null := 0; e_rc := 2; e_src := 0x7d0000000002; e_left := 16 |}.

(* The real frame [R, S), F's frame, the four blocks and the input (start, length). *)
Definition env_rangesB (e : hd_env) : list (Z * Z) :=
  [(e_R e, e_S e - e_R e); (e_F e, YG00.fs_frame_bytes (hi_cid headamp_himg_B)); (e_pp e, Layout.PP_SIZE);
   (e_pod e, e_len e); (e_out e, hd_xv e XCap33); (e_first e, hd_xv e XRc3NZ); (e_src e, e_left e)].
(* The choice: R = (S - 0x220) & -32, F aligned to its class's frame size, the four blocks 16-aligned, cap, the null
   flag and rc in range; the seven ranges lie above the image (kImgEnd) and below kHighMemEnd, pairwise apart. *)
Lemma env_segB_chk :
  (e_R env_segB =? Z.land (e_S env_segB - hi_rsz headamp_himg_B) (-32)) &&
  (e_F env_segB mod YG00.fs_frame_bytes (hi_cid headamp_himg_B) =? 0) &&
  (e_pp env_segB mod 16 =? 0) && (e_pod env_segB mod 16 =? 0) &&
  (e_out env_segB mod 16 =? 0) && (e_first env_segB mod 16 =? 0) &&
  (0 <=? e_cap env_segB) && (e_cap env_segB <=? 9) && (0 <=? e_null env_segB) && (e_null env_segB <=? 1) &&
  (-1 <=? e_rc env_segB) && (e_rc env_segB <=? e_cap env_segB) &&
  forallb (fun r => (kImgEnd <=? fst r) && (fst r + snd r <=? kHighMemEnd)) (env_rangesB env_segB) &&
  HPgSatSeg.all_apartb (env_rangesB env_segB) = true.
Proof. vm_compute. reflexivity. Qed.

(* ================================================ the witness ================================================ *)
(* The nine cut lists of headamp_himg_B. *)
Definition headamp_B_cuts : list (list (hd_loc * hd_x)) :=
  [hi_L1 headamp_himg_B; hi_L2 headamp_himg_B; hi_L3 headamp_himg_B; hi_L4 headamp_himg_B; hi_L5 headamp_himg_B;
   hi_L6 headamp_himg_B; hi_L7 headamp_himg_B; hi_L8 headamp_himg_B; hi_L9 headamp_himg_B].
(* The cells of all nine lists (a cell two lists name holds the same value in both: the computation below checks
   every list against the first value found). *)
Definition cells_segB : list (Z * Z) := flat_map (HPgSatSeg.cut_cells env_segB) headamp_B_cuts.

(* The byte at u >= SHADOW_OFF outside HPgSatU.shadow_spans_B' shadow: the frame's shadow bytes sh from
   shadow_addr F; 0 for the shadow bytes of the real-frame ranges hi_rz; the bytes of the cells of the nine cut
   lists; else none. *)
Definition byte_segB (sh : list Z) (u : Z) : option Z :=
  if (shadow_addr (e_F env_segB) <=? u) && (u <? shadow_addr (e_F env_segB) + Z.of_nat (length sh))
  then Some (nth (Z.to_nat (u - shadow_addr (e_F env_segB))) sh 0)
  else if existsb (fun z => (shadow_addr (e_R env_segB + fst z) <=? u) &&
                            (u <=? shadow_addr (e_R env_segB + fst z + snd z - 1))) (hi_rz headamp_himg_B)
  then Some 0
  else match find (fun c => (fst c <=? u) && (u <? fst c + 8)) cells_segB with
       | Some c => Some (YO0f.le_byte (snd c) 8 (Z.to_nat (u - fst c)))
       | None => None
       end.
(* The witness memory for the frame shadow pattern sh: below SHADOW_OFF only the guard's eight bytes
   (HPgSatU.guard_mem_B), so every program byte is read through mbyte's fall-back to seg_rom; above it the shadow
   bytes of the 43 globals (HPgSatU.span_shadow_B: what the runtime writes when it registers them, and the 0 of the
   freshly mapped shadow in the two gaps no descriptor covers), then byte_segB. No byte is hidden (HPgSat.H_w). *)
Definition mem_segB_of (sh : list Z) : word -> option byte := fun w =>
  if bv_unsigned w <? SHADOW_OFF then guard_mem_B (bv_unsigned w)
  else match span_shadow_B (bv_unsigned w) with
       | Some b => Some b
       | None => option_map (fun v => Z_to_bv 8 v) (byte_segB sh (bv_unsigned w))
       end.
(* After the prologue (C1 .. C5) and with the res granules in scope (C6 .. C9). *)
Definition mem_segB_A : word -> option byte := mem_segB_of (hi_shA headamp_himg_B).
Definition mem_segB_B : word -> option byte := mem_segB_of (hi_shB headamp_himg_B).

Definition regs1_segB : bvmap 5 word := HPgSatSeg.cut_regs env_segB (hi_L1 headamp_himg_B).
Definition regs2_segB : bvmap 5 word := HPgSatSeg.cut_regs env_segB (hi_L2 headamp_himg_B).
Definition regs3_segB : bvmap 5 word := HPgSatSeg.cut_regs env_segB (hi_L3 headamp_himg_B).
Definition regs4_segB : bvmap 5 word := HPgSatSeg.cut_regs env_segB (hi_L4 headamp_himg_B).
Definition regs5_segB : bvmap 5 word := HPgSatSeg.cut_regs env_segB (hi_L5 headamp_himg_B).
Definition regs6_segB : bvmap 5 word := HPgSatSeg.cut_regs env_segB (hi_L6 headamp_himg_B).
Definition regs7_segB : bvmap 5 word := HPgSatSeg.cut_regs env_segB (hi_L7 headamp_himg_B).
Definition regs8_segB : bvmap 5 word := HPgSatSeg.cut_regs env_segB (hi_L8 headamp_himg_B).
Definition regs9_segB : bvmap 5 word := HPgSatSeg.cut_regs env_segB (hi_L9 headamp_himg_B).

(* ================================ boolean checkers and their soundness ================================ *)
(* HPgSatSeg.v's strs_chk, at_chk and cut_chk, over a segment list. *)
Definition strs_chk_s (segs : list Segment) (h : word -> bool) (mem : word -> option byte) (l : list (Z * list Z)) : bool :=
  forallb (fun c => HPgSat.cstr_chk segs h mem (fst c) (snd c)) l.
Lemma strs_chk_s_ok : forall segs h mem l, strs_chk_s segs h mem l = true ->
  Forall (fun s => hd_cstr segs h mem (fst s) (snd s)) l.
Proof.
intros segs h mem l H. apply Forall_forall. intros c Hc. cbv beta. apply HPgSat.cstr_chk_ok.
unfold strs_chk_s in H. rewrite forallb_forall in H. exact (H c Hc).
Qed.
Definition at_chk_s (segs : list Segment) (h : word -> bool) (mem : word -> option byte) (regs : bvmap 5 word)
  (e : hd_env) (l : hd_loc) (v : Z) : bool :=
  match l with
  | LReg r => bv_unsigned (getr regs (Z_to_bv 5 r)) =? bv_unsigned (Z_to_bv 64 v)
  | LCell b o => HPgSat.val_chk segs (mrestrict h mem) (hd_xv e b + o) 8 (v mod 2 ^ 64)
  end.
Lemma at_chk_s_ok : forall segs h mem regs e l v, at_chk_s segs h mem regs e l v = true -> hd_at segs h mem regs e l v.
Proof.
intros segs h mem regs e [r|b o] v E; unfold at_chk_s in E; unfold hd_at.
- apply bv_eq. apply Z.eqb_eq. exact E.
- apply HPgSat.val_chk_ok. exact E.
Qed.
Definition cut_chk_s (segs : list Segment) (h : word -> bool) (mem : word -> option byte) (regs : bvmap 5 word)
  (e : hd_env) (L : list (hd_loc * hd_x)) : bool :=
  forallb (fun f => at_chk_s segs h mem regs e (fst f) (hd_xv e (snd f))) L.
Lemma cut_chk_s_ok : forall segs h mem regs e L, cut_chk_s segs h mem regs e L = true -> hd_cut segs h mem regs e L.
Proof.
intros segs h mem regs e L H. unfold hd_cut. apply Forall_forall. intros f Hf. cbv beta. apply at_chk_s_ok.
unfold cut_chk_s in H. rewrite forallb_forall in H. exact (H f Hf).
Qed.

(* Every read-only loaded segment ends at or below the guard (GUARD_B = 0x5f8210 < SHADOW_OFF; pinned image sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94). *)
Definition segsB_ro_chk : bool :=
  forallb (fun s => seg_writable s || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? GUARD_B)) Img0U.rsegs.
Lemma segsB_ro_chk_ok : segsB_ro_chk = true.
Proof. vm_compute. reflexivity. Qed.
Lemma segsB_ro_end : forall s, In s Img0U.rsegs -> seg_writable s = false ->
  Z.of_N (seg_base s) + Z.of_N (seg_size s) <= GUARD_B.
Proof.
intros s Hs Hw. pose proof segsB_ro_chk_ok as E. unfold segsB_ro_chk in E. rewrite forallb_forall in E.
specialize (E s Hs). rewrite Hw in E. cbn [orb] in E. apply Z.leb_le. exact E.
Qed.

(* Below the guard the witness reads the image. *)
Lemma mem_segB_low : forall sh a, 0 <= a < GUARD_B -> mem_segB_of sh (Z_to_bv 64 a) = None.
Proof.
intros sh a Ha. unfold mem_segB_of.
assert (Hu : bv_unsigned (Z_to_bv 64 a) = a).
{ rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). unfold GUARD_B in Ha. lia. }
assert (Hlt : (a <? SHADOW_OFF) = true) by (apply Z.ltb_lt; unfold SHADOW_OFF, GUARD_B in *; lia).
assert (Hg : (GUARD_B <=? a) = false) by (apply Z.leb_gt; lia).
rewrite Hu, Hlt. unfold guard_mem_B. rewrite Hg. reflexivity.
Qed.
Lemma aviewB_low : forall sh a, 0 <= a < GUARD_B ->
  aview Img0U.rsegs HPgSat.H_w (mem_segB_of sh) a = option_map (fun b : byte => bv_unsigned b) (seg_rom Img0U.rsegs (Z_to_bv 64 a)).
Proof. intros sh a Ha. unfold aview, mbyte, mrestrict, HPgSat.H_w. rewrite (mem_segB_low sh a Ha). reflexivity. Qed.

(* ============================== the conjuncts at the witness ============================== *)
(* The read-only data, for every symbol record B: RO_LO = 0x9c100 and RO_HI = 0x9d4e8 (.data.rel.ro start .. .got
   end, lib/AU/HPgLibU.v; pinned image sha256 53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94), and
   every read-only segment, lie below the guard. *)
Lemma aro_B : forall sh (B : asyms), arodata_okP Img0U.rsegs 0x9c100 0x9d4e8 B (aview Img0U.rsegs HPgSat.H_w (mem_segB_of sh)).
Proof.
intros sh B a Hro _ _. apply aviewB_low. hnf in Hro. destruct Hro as [(s & Hs & Hw & Hr) | Hr].
- pose proof (segsB_ro_end s Hs Hw) as Hb. pose proof (N2Z.is_nonneg (seg_base s)) as H0. lia.
- unfold GUARD_B. lia.
Qed.

(* Every byte of a read-only segment reads as the image's, at every world whose hidden set is H_w. *)
Lemma rom_B : forall sh (W : world Img0U.rsegs), w_H W = HPgSat.H_w -> rom_view Img0U.rsegs W (mem_segB_of sh).
Proof.
intros sh W HW a Ha. rewrite HW. apply aviewB_low. hnf in Ha. destruct Ha as (s & Hs & Hw & Hr).
pose proof (segsB_ro_end s Hs Hw) as Hb. pose proof (N2Z.is_nonneg (seg_base s)) as H0. lia.
Qed.

(* sp holds R at every cut's register map. *)
Definition headamp_B_regs : list (bvmap 5 word) :=
  [regs1_segB; regs2_segB; regs3_segB; regs4_segB; regs5_segB; regs6_segB; regs7_segB; regs8_segB; regs9_segB].
Lemma sp_B_chk : forallb (fun r => bv_unsigned (getr r 2) =? bv_unsigned (w64 (e_R env_segB))) headamp_B_regs = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sp_B : Forall (fun r => getr r 2 = w64 (e_R env_segB)) headamp_B_regs.
Proof.
apply Forall_forall. intros r Hr. cbv beta. pose proof sp_B_chk as E. rewrite forallb_forall in E.
specialize (E r Hr). cbv beta in E. apply bv_eq. apply Z.eqb_eq. exact E.
Qed.

(* The input range lies apart from the callees' stack below R, the ranges M01 writes (hi_w1) and the pp block. *)
Lemma src_apartB_chk :
  HPgSatSeg.rng_apartb (e_src env_segB, e_left env_segB) (e_R env_segB - T_SEG_STK, T_SEG_STK) &&
  forallb (fun w => HPgSatSeg.rng_apartb (e_src env_segB, e_left env_segB) (hd_xv env_segB (fst (fst w)) + snd (fst w), snd w))
    (hi_w1 headamp_himg_B) &&
  HPgSatSeg.rng_apartb (e_src env_segB, e_left env_segB) (e_pp env_segB, Layout.PP_SIZE) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma src_apart_B : forall a, e_src env_segB <= a < e_src env_segB + e_left env_segB ->
  ~ (e_R env_segB - T_SEG_STK <= a < e_R env_segB) /\ ~ hd_inw env_segB (hi_w1 headamp_himg_B) a /\
  ~ (e_pp env_segB <= a < e_pp env_segB + Layout.PP_SIZE).
Proof.
intros a Ha. pose proof src_apartB_chk as E. rewrite !andb_true_iff in E. destruct E as [[E1 E2] E3].
split; [|split].
- pose proof (HPgSatSeg.rng_apartb_ok _ _ _ _ E1 a Ha) as P. intro Hb. apply P. lia.
- intro Hw. unfold hd_inw in Hw. apply Exists_exists in Hw. destruct Hw as (w & Hin & Hr).
  rewrite forallb_forall in E2. exact (HPgSatSeg.rng_apartb_ok _ _ _ _ (E2 w Hin) a Ha Hr).
- exact (HPgSatSeg.rng_apartb_ok _ _ _ _ E3 a Ha).
Qed.

(* The run's quantities: what hd_seg_pre and the five contracts ask of e alone. *)
Ltac zbB := first [apply Z.eqb_eq | apply Z.leb_le | apply Z.ltb_lt | apply Z.eqb_neq | apply HPgSat.amem_rangeb_ok];
  vm_compute; reflexivity.
Lemma env_B :
  e_R env_segB mod 32 = 0 /\ e_R env_segB + hi_rsz headamp_himg_B <= e_S env_segB /\
  0 <= e_cap env_segB <= 9 /\ 0 <= e_null env_segB <= 1 /\ -1 <= e_rc env_segB <= e_cap env_segB /\
  e_pp env_segB <> 0 /\ e_pod env_segB <> 0 /\ e_out env_segB <> 0 /\ e_first env_segB <> 0 /\
  e_pod env_segB mod 16 = 0 /\ amem_range (e_pod env_segB) (e_len env_segB + 8) /\
  0 < e_src env_segB /\ e_src env_segB + e_left env_segB <= 2 ^ 63 /\ amem_range (e_src env_segB) (e_left env_segB).
Proof.
split; [zbB|]. split; [zbB|].
split; [split; zbB|]. split; [split; zbB|]. split; [split; zbB|].
split; [zbB|]. split; [zbB|]. split; [zbB|]. split; [zbB|].
split; [zbB|]. split; [zbB|].
split; [zbB|]. split; [zbB | zbB].
Qed.

(* ================================================ the lemma ================================================ *)
(* The memory-dependent conjuncts at mem_segB_of sh, one checker each. *)
Definition fsh_atB (sh : list Z) : bool :=
  HPgSat.bytes_chk (aview Img0U.rsegs HPgSat.H_w (mem_segB_of sh)) (shadow_addr (e_F env_segB)) sh.
Definition globs_atB (sh : list Z) : bool :=
  HPgSatSeg.ranges_chk (aview Img0U.rsegs HPgSat.H_w (mem_segB_of sh)) (fun a => a) (hi_globs headamp_himg_B).
Definition rz_atB (sh : list Z) : bool :=
  HPgSatSeg.ranges_chk (aview Img0U.rsegs HPgSat.H_w (mem_segB_of sh)) (fun o => e_R env_segB + o) (hi_rz headamp_himg_B).
Definition strs_atB (sh : list Z) : bool := strs_chk_s Img0U.rsegs HPgSat.H_w (mem_segB_of sh) (hi_strs headamp_himg_B).
Definition cells_atB (sh : list Z) : bool :=
  HPgSat.cells_chk Img0U.rsegs (mrestrict HPgSat.H_w (mem_segB_of sh)) (hi_cells headamp_himg_B).
Definition guard_atB (sh : list Z) : bool :=
  HPgSat.guard_chk (aview Img0U.rsegs HPgSat.H_w (mem_segB_of sh)) (hi_gotw headamp_himg_B) (hi_guard headamp_himg_B).
Definition cuts_atB (sh : list Z) : bool :=
  cut_chk_s Img0U.rsegs HPgSat.H_w (mem_segB_of sh) regs1_segB env_segB (hi_L1 headamp_himg_B) &&
  cut_chk_s Img0U.rsegs HPgSat.H_w (mem_segB_of sh) regs2_segB env_segB (hi_L2 headamp_himg_B) &&
  cut_chk_s Img0U.rsegs HPgSat.H_w (mem_segB_of sh) regs3_segB env_segB (hi_L3 headamp_himg_B) &&
  cut_chk_s Img0U.rsegs HPgSat.H_w (mem_segB_of sh) regs4_segB env_segB (hi_L4 headamp_himg_B) &&
  cut_chk_s Img0U.rsegs HPgSat.H_w (mem_segB_of sh) regs5_segB env_segB (hi_L5 headamp_himg_B) &&
  cut_chk_s Img0U.rsegs HPgSat.H_w (mem_segB_of sh) regs6_segB env_segB (hi_L6 headamp_himg_B) &&
  cut_chk_s Img0U.rsegs HPgSat.H_w (mem_segB_of sh) regs7_segB env_segB (hi_L7 headamp_himg_B) &&
  cut_chk_s Img0U.rsegs HPgSat.H_w (mem_segB_of sh) regs8_segB env_segB (hi_L8 headamp_himg_B) &&
  cut_chk_s Img0U.rsegs HPgSat.H_w (mem_segB_of sh) regs9_segB env_segB (hi_L9 headamp_himg_B).

(* At any pattern sh whose seven checks pass, (H_w, mem_segB_of sh, regs1_segB .. regs9_segB, env_segB) is the
   state of HPgSatSeg.hd_seg_static at image B. *)
Lemma seg_static_ofB : forall sh,
  fsh_atB sh = true -> globs_atB sh = true -> rz_atB sh = true -> strs_atB sh = true ->
  cells_atB sh = true -> guard_atB sh = true -> cuts_atB sh = true ->
  HPgSatSeg.hd_seg_static Img0U.rsegs headamp_himg_B sh 0x9c100 0x9d4e8.
Proof.
intros sh F G Z S C U K.
unfold fsh_atB, globs_atB, rz_atB, strs_atB, cells_atB, guard_atB, cuts_atB in *.
rewrite !andb_true_iff in K. destruct K as [[[[[[[[K1 K2] K3] K4] K5] K6] K7] K8] K9].
unfold HPgSatSeg.hd_seg_static.
exists HPgSat.H_w, (mem_segB_of sh), regs1_segB, regs2_segB, regs3_segB, regs4_segB, regs5_segB, regs6_segB,
  regs7_segB, regs8_segB, regs9_segB, env_segB.
split; [unfold hd_fsh; exact (HPgSat.bytes_chk_ok _ _ _ F)|].
split; [exact (HPgSatSeg.ranges_chk_ok _ _ _ G)|].
split; [exact (HPgSatSeg.ranges_chk_ok _ _ _ Z)|].
split; [exact (strs_chk_s_ok _ _ _ _ S)|].
split; [unfold hd_ro_cells; exact (HPgSat.cells_chk_ok _ _ _ C)|].
split; [exact (aro_B sh)|].
split; [exact (HPgSat.guard_chk_ok _ _ _ U)|].
split; [exact (rom_B sh)|].
split; [exact (cut_chk_s_ok _ _ _ _ _ _ K1)|]. split; [exact (cut_chk_s_ok _ _ _ _ _ _ K2)|].
split; [exact (cut_chk_s_ok _ _ _ _ _ _ K3)|]. split; [exact (cut_chk_s_ok _ _ _ _ _ _ K4)|].
split; [exact (cut_chk_s_ok _ _ _ _ _ _ K5)|]. split; [exact (cut_chk_s_ok _ _ _ _ _ _ K6)|].
split; [exact (cut_chk_s_ok _ _ _ _ _ _ K7)|]. split; [exact (cut_chk_s_ok _ _ _ _ _ _ K8)|].
split; [exact (cut_chk_s_ok _ _ _ _ _ _ K9)|].
split; [exact sp_B|].
destruct env_B as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14).
split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
split; [exact E6|]. split; [exact E7|]. split; [exact E8|]. split; [exact E9|]. split; [exact E10|].
split; [exact E11|]. split; [exact E12|]. split; [exact E13|]. split; [exact E14|].
exact src_apart_B.
Qed.

(* After the prologue (the shadow pattern of C1 .. C5, which headamp_build_contract, headamp_dup_contract and
   headamp_check_contract take in hd_seg_pre). *)
Lemma fsh_atB_A : fsh_atB (hi_shA headamp_himg_B) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma globs_atB_A : globs_atB (hi_shA headamp_himg_B) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rz_atB_A : rz_atB (hi_shA headamp_himg_B) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma strs_atB_A : strs_atB (hi_shA headamp_himg_B) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cells_atB_A : cells_atB (hi_shA headamp_himg_B) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma guard_atB_A : guard_atB (hi_shA headamp_himg_B) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cuts_atB_A : cuts_atB (hi_shA headamp_himg_B) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma headamp_seg_static_B : HPgSatSeg.hd_seg_static Img0U.rsegs headamp_himg_B (hi_shA headamp_himg_B) 0x9c100 0x9d4e8.
Proof. exact (seg_static_ofB _ fsh_atB_A globs_atB_A rz_atB_A strs_atB_A cells_atB_A guard_atB_A cuts_atB_A). Qed.
Print Assumptions headamp_seg_static_B.

(* With the res granules 0x54 and 0x55 in scope (0x00 and 0x04: the shadow pattern of C6 .. C9, which
   headamp_first_contract and headamp_plain_contract take in hd_seg_pre): the same state, with mem_segB_B. *)
Lemma fsh_atB_B : fsh_atB (hi_shB headamp_himg_B) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma globs_atB_B : globs_atB (hi_shB headamp_himg_B) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rz_atB_B : rz_atB (hi_shB headamp_himg_B) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma strs_atB_B : strs_atB (hi_shB headamp_himg_B) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cells_atB_B : cells_atB (hi_shB headamp_himg_B) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma guard_atB_B : guard_atB (hi_shB headamp_himg_B) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cuts_atB_B : cuts_atB (hi_shB headamp_himg_B) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma headamp_seg_static_B_shB : HPgSatSeg.hd_seg_static Img0U.rsegs headamp_himg_B (hi_shB headamp_himg_B) 0x9c100 0x9d4e8.
Proof. exact (seg_static_ofB _ fsh_atB_B globs_atB_B rz_atB_B strs_atB_B cells_atB_B guard_atB_B cuts_atB_B). Qed.
Print Assumptions headamp_seg_static_B_shB.

(* mem_segB_B differs from mem_segB_A at the two shadow bytes of the res granules only. *)
Lemma headamp_seg_shB_B : forall w, bv_unsigned w <> shadow_addr (e_F env_segB) + 0x54 ->
  bv_unsigned w <> shadow_addr (e_F env_segB) + 0x55 -> mem_segB_B w = mem_segB_A w.
Proof.
intros w H54 H55. unfold mem_segB_B, mem_segB_A, mem_segB_of.
destruct (bv_unsigned w <? SHADOW_OFF); [reflexivity|].
destruct (span_shadow_B (bv_unsigned w)); [reflexivity|].
f_equal. unfold byte_segB.
destruct ((shadow_addr (e_F env_segB) <=? bv_unsigned w) &&
          (bv_unsigned w <? shadow_addr (e_F env_segB) + Z.of_nat (length (hi_shA headamp_himg_B)))) eqn:EA.
- assert (Hl : length (hi_shB headamp_himg_B) = length (hi_shA headamp_himg_B)) by reflexivity.
  rewrite Hl, EA. f_equal.
  apply andb_prop in EA. destruct EA as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  change (length (hi_shA headamp_himg_B)) with 116%nat in E2. change (Z.of_nat 116) with 116 in E2.
  set (i := Z.to_nat (bv_unsigned w - shadow_addr (e_F env_segB))).
  assert (Hi : (i < 116)%nat) by (subst i; lia).
  assert (H84 : i <> 84%nat) by (subst i; lia).
  assert (H85 : i <> 85%nat) by (subst i; lia).
  clearbody i. clear - Hi H84 H85.
  do 116 (destruct i as [|i]; [reflexivity || (exfalso; lia)|]). lia.
- assert (Hl : length (hi_shB headamp_himg_B) = length (hi_shA headamp_himg_B)) by reflexivity.
  rewrite Hl, EA. reflexivity.
Qed.
Print Assumptions headamp_seg_shB_B.
