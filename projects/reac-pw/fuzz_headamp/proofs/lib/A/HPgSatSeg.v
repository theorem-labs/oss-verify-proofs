(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgSatSeg.v at 0de5d668c87 for
   reac-pw/fuzz_headamp image A (fuzz_headamp.asan): module paths changed, the rl_ / role_ prefixes renamed to hd_ /
   headamp_, image A's segments read from lib/A/Img0.v; the 43 descriptors, the shadow spans, granule_shadow and the
   guard's bytes are lib/A/HPgSat.v's (no second copy); headamp's run quantities (four blocks, the cap, the null flag,
   the parse's answer) in place of role's two blocks and flags byte; the nine cut lists hi_L1 .. hi_L9 in place of
   role's two; the stack-guard conjunct is new; the witness memory is a function of the frame's shadow pattern, so the
   whole state is given at hi_shA and at hi_shB (role gives hi_shB as one changed byte). *)
(* Image A's witness for the image-level premises of reac-pw/fuzz_headamp's five segment contracts (lib/A/HPgCSpec.v:
   the image-level conjuncts of hd_seg_pre, the cut lists hi_L1 .. hi_L9, and what headamp_build_contract ..
   headamp_plain_contract ask of the run's quantities alone) at I = headamp_himg_A (lib/A/HPgImgA.v). At one
   concrete state over image A's loaded segments, the frame's shadow bytes, the 43 registered globals, the checked
   real-frame range, the 36 strings, the read-only cells, the read-only data, the stack-guard cells, the read-only
   segments and the live values at all nine cuts hold together, so those premises are not vacuous on image A; the
   same state with the res granules in scope gives them at hi_shB. Each shadow byte the witness memory holds is the
   one the runtime writes, and each program byte is read from the image.
   Pinned image: fuzz_headamp.asan, sha256 f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47.
   proves no function (kind: statement text) *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YP09 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YO0f YG00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgImgA Img0 HPgSat.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ======================================== the registered globals ======================================== *)
(* The 43 rows of HPgSat.headamp_A_globals (each the image's descriptor, HPgSat.headamp_A_globals_chk; the table the
   runtime registers, HPgSat.headamp_A_reg_chk; the rows of hi_globs, HPgSat.headamp_A_globals_globs): their ranges
   [beg, beg + size_with_redzone) are ascending and apart (so each granule has at most one global's shadow byte) and
   lie in HPgSat.shadow_spans; each string of hi_strs is in the image with its NUL and is the global with beg = its
   address and size = its length + 1 (cstrs_img_chk). *)
Lemma headamp_A_globals_apart_chk :
  forallb (fun k => let '(_, (b1, _, r1)) := nth k headamp_A_globals gdummy in
                    let '(_, (b2, _, _)) := nth (S k) headamp_A_globals gdummy in b1 + r1 <=? b2) (seq 0 42) &&
  forallb (fun g => let '(_, (b, _, r)) := g in existsb (fun s => (fst s <=? b) && (b + r <=? snd s)) shadow_spans)
    headamp_A_globals &&
  cstrs_img_chk Img0.rsegs headamp_A_globals (hi_strs headamp_himg_A) = true.
Proof. vm_compute. reflexivity. Qed.

(* ======================================== the run's quantities ======================================== *)
(* S the entry sp (a user stack address); R = (S - 0x1e0) & -32 (the prologue's s1, HPgImgA.v's header, pinned image
   sha256 f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47); F a class-4 side-stack frame for locals
   (1024-byte frames, 1024-aligned); the four blocks the harness allocates, each 16-aligned as the allocator returns
   them: pp (19744 bytes), pod (len), out (3 cap + 3) and first (3 max(rc, 0), or 1 when that is 0); the input after
   the two harness bytes at src (left bytes). len = 16, cap = 3, the null flag 0 and the parse's answer rc = 2 are
   chosen in the ranges the contracts ask (0 <= cap <= 9, 0 <= null <= 1, -1 <= rc <= cap); no conjunct below ties
   len or rc to an input. *)
Definition env_seg : hd_env := {|
  e_S := 0x7fffffff0000; e_R := 0x7ffffffefe20; e_F := 0x7ff000000000;
  e_pp := 0x7e0000000010; e_pod := 0x7e0000010010; e_out := 0x7e0000020010; e_first := 0x7e0000030010;
  e_len := 16; e_cap := 3; e_null := 0; e_rc := 2; e_src := 0x7d0000000002; e_left := 16 |}.

Definition rng_apartb (r1 r2 : Z * Z) : bool := (fst r1 + snd r1 <=? fst r2) || (fst r2 + snd r2 <=? fst r1).
Fixpoint all_apartb (l : list (Z * Z)) : bool :=
  match l with [] => true | r :: t => forallb (rng_apartb r) t && all_apartb t end.
Lemma rng_apartb_ok : forall p n q m, rng_apartb (p, n) (q, m) = true ->
  forall a, p <= a < p + n -> ~ (q <= a < q + m).
Proof.
intros p n q m H a Ha Hb. unfold rng_apartb in H. cbn [fst snd] in H. apply orb_true_iff in H.
destruct H as [H|H]; apply Z.leb_le in H; lia.
Qed.
(* The real frame [R, S), F's frame, the four blocks and the input (start, length). *)
Definition env_ranges (e : hd_env) : list (Z * Z) :=
  [(e_R e, e_S e - e_R e); (e_F e, YG00.fs_frame_bytes (hi_cid headamp_himg_A)); (e_pp e, Layout.PP_SIZE);
   (e_pod e, e_len e); (e_out e, hd_xv e XCap33); (e_first e, hd_xv e XRc3NZ); (e_src e, e_left e)].
(* The choice: R = (S - 0x1e0) & -32, F aligned to its class's frame size, the four blocks 16-aligned, cap, the null
   flag and rc in range; the seven ranges lie above the image (kImgEnd) and below kHighMemEnd, pairwise apart. *)
Lemma env_seg_chk :
  (e_R env_seg =? Z.land (e_S env_seg - hi_rsz headamp_himg_A) (-32)) &&
  (e_F env_seg mod YG00.fs_frame_bytes (hi_cid headamp_himg_A) =? 0) &&
  (e_pp env_seg mod 16 =? 0) && (e_pod env_seg mod 16 =? 0) &&
  (e_out env_seg mod 16 =? 0) && (e_first env_seg mod 16 =? 0) &&
  (0 <=? e_cap env_seg) && (e_cap env_seg <=? 9) && (0 <=? e_null env_seg) && (e_null env_seg <=? 1) &&
  (-1 <=? e_rc env_seg) && (e_rc env_seg <=? e_cap env_seg) &&
  forallb (fun r => (kImgEnd <=? fst r) && (fst r + snd r <=? kHighMemEnd)) (env_ranges env_seg) &&
  all_apartb (env_ranges env_seg) = true.
Proof. vm_compute. reflexivity. Qed.

(* ================================================ the witness ================================================ *)
(* The nine cut lists of headamp_himg_A. *)
Definition headamp_A_cuts : list (list (hd_loc * hd_x)) :=
  [hi_L1 headamp_himg_A; hi_L2 headamp_himg_A; hi_L3 headamp_himg_A; hi_L4 headamp_himg_A; hi_L5 headamp_himg_A;
   hi_L6 headamp_himg_A; hi_L7 headamp_himg_A; hi_L8 headamp_himg_A; hi_L9 headamp_himg_A].
(* The real-frame cells (address, 8-byte value) that a cut list L names, at e. *)
Definition cut_cells (e : hd_env) (L : list (hd_loc * hd_x)) : list (Z * Z) :=
  flat_map (fun f => match fst f with
                     | LCell b o => [(hd_xv e b + o, hd_xv e (snd f) mod 2 ^ 64)]
                     | LReg _ => []
                     end) L.
(* The cells of all nine lists (a cell two lists name holds the same value in both: the computation below checks
   every list against the first value found). *)
Definition cells_seg : list (Z * Z) := flat_map (cut_cells env_seg) headamp_A_cuts.

(* The byte at u >= SHADOW_OFF outside HPgSat.shadow_spans' shadow: the frame's shadow bytes sh from shadow_addr F;
   0 for the shadow bytes of the real-frame ranges hi_rz; the bytes of the cells of the nine cut lists; else none. *)
Definition byte_seg (sh : list Z) (u : Z) : option Z :=
  if (shadow_addr (e_F env_seg) <=? u) && (u <? shadow_addr (e_F env_seg) + Z.of_nat (length sh))
  then Some (nth (Z.to_nat (u - shadow_addr (e_F env_seg))) sh 0)
  else if existsb (fun z => (shadow_addr (e_R env_seg + fst z) <=? u) &&
                            (u <=? shadow_addr (e_R env_seg + fst z + snd z - 1))) (hi_rz headamp_himg_A)
  then Some 0
  else match find (fun c => (fst c <=? u) && (u <? fst c + 8)) cells_seg with
       | Some c => Some (YO0f.le_byte (snd c) 8 (Z.to_nat (u - fst c)))
       | None => None
       end.
(* The witness memory for the frame shadow pattern sh: below SHADOW_OFF only the guard's eight bytes
   (HPgSat.guard_mem), so every program byte is read through mbyte's fall-back to seg_rom; above it the shadow bytes
   of the 43 globals (HPgSat.span_shadow: what the runtime writes when it registers them, and the 0 of the freshly
   mapped shadow in the two gaps no descriptor covers), then byte_seg. No byte is hidden (HPgSat.H_w). *)
Definition mem_seg_of (sh : list Z) : word -> option byte := fun w =>
  if bv_unsigned w <? SHADOW_OFF then guard_mem (bv_unsigned w)
  else match span_shadow (bv_unsigned w) with
       | Some b => Some b
       | None => option_map (fun v => Z_to_bv 8 v) (byte_seg sh (bv_unsigned w))
       end.
(* After the prologue (C1 .. C5) and with the res granules in scope (C6 .. C9). *)
Definition mem_seg : word -> option byte := mem_seg_of (hi_shA headamp_himg_A).
Definition mem_segB : word -> option byte := mem_seg_of (hi_shB headamp_himg_A).

(* The register map at a cut: each register L names holds the value L gives at e, and sp holds R. *)
Definition cut_regs (e : hd_env) (L : list (hd_loc * hd_x)) : bvmap 5 word :=
  fold_right (fun f m => match fst f with
                         | LReg r => regupd m (Z_to_bv 5 r) (Z_to_bv 64 (hd_xv e (snd f)))
                         | LCell _ _ => m
                         end)
    (regupd bvmap_empty (Z_to_bv 5 2) (Z_to_bv 64 (e_R e))) L.
Definition regs1_seg : bvmap 5 word := cut_regs env_seg (hi_L1 headamp_himg_A).
Definition regs2_seg : bvmap 5 word := cut_regs env_seg (hi_L2 headamp_himg_A).
Definition regs3_seg : bvmap 5 word := cut_regs env_seg (hi_L3 headamp_himg_A).
Definition regs4_seg : bvmap 5 word := cut_regs env_seg (hi_L4 headamp_himg_A).
Definition regs5_seg : bvmap 5 word := cut_regs env_seg (hi_L5 headamp_himg_A).
Definition regs6_seg : bvmap 5 word := cut_regs env_seg (hi_L6 headamp_himg_A).
Definition regs7_seg : bvmap 5 word := cut_regs env_seg (hi_L7 headamp_himg_A).
Definition regs8_seg : bvmap 5 word := cut_regs env_seg (hi_L8 headamp_himg_A).
Definition regs9_seg : bvmap 5 word := cut_regs env_seg (hi_L9 headamp_himg_A).

(* ================================ boolean checkers and their soundness ================================ *)
(* range_addressable over a list of (start, length) ranges, each start moved by f. *)
Definition ranges_chk (rd : reader) (f : Z -> Z) (l : list (Z * Z)) : bool :=
  forallb (fun g => (0 <=? snd g) && ra_chk rd SHADOW_OFF (f (fst g)) (Z.to_nat (snd g))) l.
Lemma ranges_chk_ok : forall rd f l, ranges_chk rd f l = true ->
  Forall (fun g => range_addressable rd SHADOW_OFF (f (fst g)) (snd g)) l.
Proof.
intros rd f l H. apply Forall_forall. intros g Hg. cbv beta. unfold ranges_chk in H. rewrite forallb_forall in H.
specialize (H g Hg). cbv beta in H. apply andb_prop in H. destruct H as [H1 H2]. apply Z.leb_le in H1.
apply (ra_chk_ok _ _ _ (Z.to_nat (snd g))); [apply Z2Nat.id; exact H1 | exact H2].
Qed.

(* hd_cstr for each string of a list. *)
Definition strs_chk (h : word -> bool) (mem : word -> option byte) (l : list (Z * list Z)) : bool :=
  forallb (fun c => cstr_chk Img0.rsegs h mem (fst c) (snd c)) l.
Lemma strs_chk_ok : forall h mem l, strs_chk h mem l = true ->
  Forall (fun s => hd_cstr Img0.rsegs h mem (fst s) (snd s)) l.
Proof.
intros h mem l H. apply Forall_forall. intros c Hc. cbv beta. apply cstr_chk_ok.
unfold strs_chk in H. rewrite forallb_forall in H. exact (H c Hc).
Qed.

(* HPgBase.hd_at and hd_cut. *)
Definition at_chk (h : word -> bool) (mem : word -> option byte) (regs : bvmap 5 word) (e : hd_env)
  (l : hd_loc) (v : Z) : bool :=
  match l with
  | LReg r => bv_unsigned (getr regs (Z_to_bv 5 r)) =? bv_unsigned (Z_to_bv 64 v)
  | LCell b o => val_chk Img0.rsegs (mrestrict h mem) (hd_xv e b + o) 8 (v mod 2 ^ 64)
  end.
Lemma at_chk_ok : forall h mem regs e l v, at_chk h mem regs e l v = true -> hd_at Img0.rsegs h mem regs e l v.
Proof.
intros h mem regs e [r|b o] v E; unfold at_chk in E; unfold hd_at.
- apply bv_eq. apply Z.eqb_eq. exact E.
- apply val_chk_ok. exact E.
Qed.
Definition cut_chk (h : word -> bool) (mem : word -> option byte) (regs : bvmap 5 word) (e : hd_env)
  (L : list (hd_loc * hd_x)) : bool :=
  forallb (fun f => at_chk h mem regs e (fst f) (hd_xv e (snd f))) L.
Lemma cut_chk_ok : forall h mem regs e L, cut_chk h mem regs e L = true -> hd_cut Img0.rsegs h mem regs e L.
Proof.
intros h mem regs e L H. unfold hd_cut. apply Forall_forall. intros f Hf. cbv beta. apply at_chk_ok.
unfold cut_chk in H. rewrite forallb_forall in H. exact (H f Hf).
Qed.

(* Every read-only loaded segment ends at or below the guard (GUARD = 0x5f7d90 < SHADOW_OFF; pinned image sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47). *)
Definition segsA_ro_chk : bool :=
  forallb (fun s => seg_writable s || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? GUARD)) Img0.rsegs.
Lemma segsA_ro_chk_ok : segsA_ro_chk = true.
Proof. vm_compute. reflexivity. Qed.
Lemma segsA_ro_end : forall s, In s Img0.rsegs -> seg_writable s = false ->
  Z.of_N (seg_base s) + Z.of_N (seg_size s) <= GUARD.
Proof.
intros s Hs Hw. pose proof segsA_ro_chk_ok as E. unfold segsA_ro_chk in E. rewrite forallb_forall in E.
specialize (E s Hs). rewrite Hw in E. cbn [orb] in E. apply Z.leb_le. exact E.
Qed.

(* Below the guard the witness reads the image. *)
Lemma mem_seg_low : forall sh a, 0 <= a < GUARD -> mem_seg_of sh (Z_to_bv 64 a) = None.
Proof.
intros sh a Ha. unfold mem_seg_of.
assert (Hu : bv_unsigned (Z_to_bv 64 a) = a).
{ rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). unfold GUARD in Ha. lia. }
assert (Hlt : (a <? SHADOW_OFF) = true) by (apply Z.ltb_lt; unfold SHADOW_OFF, GUARD in *; lia).
assert (Hg : (GUARD <=? a) = false) by (apply Z.leb_gt; lia).
rewrite Hu, Hlt. unfold guard_mem. rewrite Hg. reflexivity.
Qed.
Lemma aview_low : forall sh a, 0 <= a < GUARD ->
  aview Img0.rsegs H_w (mem_seg_of sh) a = option_map (fun b : byte => bv_unsigned b) (seg_rom Img0.rsegs (Z_to_bv 64 a)).
Proof. intros sh a Ha. unfold aview, mbyte, mrestrict, H_w. rewrite (mem_seg_low sh a Ha). reflexivity. Qed.

(* ============================== the conjuncts at the witness ============================== *)
(* The read-only data, for every symbol record B: RO_LO = 0x9bc80 and RO_HI = 0x9d068 (.data.rel.ro start .. .got
   end, lib/A/HPgLib.v; pinned image sha256 f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47), and
   every read-only segment, lie below the guard. *)
Lemma aro_A : forall sh (B : asyms), arodata_okP Img0.rsegs 0x9bc80 0x9d068 B (aview Img0.rsegs H_w (mem_seg_of sh)).
Proof.
intros sh B a Hro _ _. apply aview_low. hnf in Hro. destruct Hro as [(s & Hs & Hw & Hr) | Hr].
- pose proof (segsA_ro_end s Hs Hw) as Hb. pose proof (N2Z.is_nonneg (seg_base s)) as H0. lia.
- unfold GUARD. lia.
Qed.

(* Every byte of a read-only segment reads as the image's, at every world whose hidden set is H_w. *)
Lemma rom_A : forall sh (W : world Img0.rsegs), w_H W = H_w -> rom_view Img0.rsegs W (mem_seg_of sh).
Proof.
intros sh W HW a Ha. rewrite HW. apply aview_low. hnf in Ha. destruct Ha as (s & Hs & Hw & Hr).
pose proof (segsA_ro_end s Hs Hw) as Hb. pose proof (N2Z.is_nonneg (seg_base s)) as H0. lia.
Qed.

(* sp holds R at every cut's register map. *)
Definition headamp_A_regs : list (bvmap 5 word) :=
  [regs1_seg; regs2_seg; regs3_seg; regs4_seg; regs5_seg; regs6_seg; regs7_seg; regs8_seg; regs9_seg].
Lemma sp_A_chk : forallb (fun r => bv_unsigned (getr r 2) =? bv_unsigned (w64 (e_R env_seg))) headamp_A_regs = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sp_A : Forall (fun r => getr r 2 = w64 (e_R env_seg)) headamp_A_regs.
Proof.
apply Forall_forall. intros r Hr. cbv beta. pose proof sp_A_chk as E. rewrite forallb_forall in E.
specialize (E r Hr). cbv beta in E. apply bv_eq. apply Z.eqb_eq. exact E.
Qed.

(* The input range lies apart from the callees' stack below R, the ranges M01 writes (hi_w1) and the pp block. *)
Lemma src_apart_chk :
  rng_apartb (e_src env_seg, e_left env_seg) (e_R env_seg - T_SEG_STK, T_SEG_STK) &&
  forallb (fun w => rng_apartb (e_src env_seg, e_left env_seg) (hd_xv env_seg (fst (fst w)) + snd (fst w), snd w))
    (hi_w1 headamp_himg_A) &&
  rng_apartb (e_src env_seg, e_left env_seg) (e_pp env_seg, Layout.PP_SIZE) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma src_apart_A : forall a, e_src env_seg <= a < e_src env_seg + e_left env_seg ->
  ~ (e_R env_seg - T_SEG_STK <= a < e_R env_seg) /\ ~ hd_inw env_seg (hi_w1 headamp_himg_A) a /\
  ~ (e_pp env_seg <= a < e_pp env_seg + Layout.PP_SIZE).
Proof.
intros a Ha. pose proof src_apart_chk as E. rewrite !andb_true_iff in E. destruct E as [[E1 E2] E3].
split; [|split].
- pose proof (rng_apartb_ok _ _ _ _ E1 a Ha) as P. intro Hb. apply P. lia.
- intro Hw. unfold hd_inw in Hw. apply Exists_exists in Hw. destruct Hw as (w & Hin & Hr).
  rewrite forallb_forall in E2. exact (rng_apartb_ok _ _ _ _ (E2 w Hin) a Ha Hr).
- exact (rng_apartb_ok _ _ _ _ E3 a Ha).
Qed.

(* The run's quantities: what hd_seg_pre and the five contracts ask of e alone. *)
Ltac zb := first [apply Z.eqb_eq | apply Z.leb_le | apply Z.ltb_lt | apply Z.eqb_neq | apply amem_rangeb_ok];
  vm_compute; reflexivity.
Lemma env_A :
  e_R env_seg mod 32 = 0 /\ e_R env_seg + hi_rsz headamp_himg_A <= e_S env_seg /\
  0 <= e_cap env_seg <= 9 /\ 0 <= e_null env_seg <= 1 /\ -1 <= e_rc env_seg <= e_cap env_seg /\
  e_pp env_seg <> 0 /\ e_pod env_seg <> 0 /\ e_out env_seg <> 0 /\ e_first env_seg <> 0 /\
  e_pod env_seg mod 16 = 0 /\ amem_range (e_pod env_seg) (e_len env_seg + 8) /\
  0 < e_src env_seg /\ e_src env_seg + e_left env_seg <= 2 ^ 63 /\ amem_range (e_src env_seg) (e_left env_seg).
Proof.
split; [zb|]. split; [zb|].
split; [split; zb|]. split; [split; zb|]. split; [split; zb|].
split; [zb|]. split; [zb|]. split; [zb|]. split; [zb|].
split; [zb|]. split; [zb|].
split; [zb|]. split; [zb | zb].
Qed.

(* ================================================ the lemma ================================================ *)
(* The image-level conjuncts of hd_seg_pre at I with the frame shadow pattern sh (RLO, RHI the read-only window),
   the nine cut lists of I with sp = R at each cut's register map, and what the five segment contracts ask of the
   run's quantities alone, together at one state (H, mem, r1 .. r9, e). *)
Definition hd_seg_static (segs : list Segment) (I : hd_himg) (sh : list Z) (RLO RHI : Z) : Prop :=
  exists (H : word -> bool) (mem : word -> option byte) (r1 r2 r3 r4 r5 r6 r7 r8 r9 : bvmap 5 word) (e : hd_env),
  hd_fsh segs H mem (e_F e) sh /\
  Forall (fun g => range_addressable (aview segs H mem) SHADOW_OFF (fst g) (snd g)) (hi_globs I) /\
  Forall (fun z => range_addressable (aview segs H mem) SHADOW_OFF (e_R e + fst z) (snd z)) (hi_rz I) /\
  Forall (fun s => hd_cstr segs H mem (fst s) (snd s)) (hi_strs I) /\
  hd_ro_cells segs H mem (hi_cells I) /\
  (forall B : asyms, arodata_okP segs RLO RHI B (aview segs H mem)) /\
  hd_guard_ok (aview segs H mem) (hi_gotw I) (hi_guard I) /\
  (forall W : world segs, w_H W = H -> rom_view segs W mem) /\
  hd_cut segs H mem r1 e (hi_L1 I) /\ hd_cut segs H mem r2 e (hi_L2 I) /\ hd_cut segs H mem r3 e (hi_L3 I) /\
  hd_cut segs H mem r4 e (hi_L4 I) /\ hd_cut segs H mem r5 e (hi_L5 I) /\ hd_cut segs H mem r6 e (hi_L6 I) /\
  hd_cut segs H mem r7 e (hi_L7 I) /\ hd_cut segs H mem r8 e (hi_L8 I) /\ hd_cut segs H mem r9 e (hi_L9 I) /\
  Forall (fun r => getr r 2 = w64 (e_R e)) [r1; r2; r3; r4; r5; r6; r7; r8; r9] /\
  e_R e mod 32 = 0 /\ e_R e + hi_rsz I <= e_S e /\
  0 <= e_cap e <= 9 /\ 0 <= e_null e <= 1 /\ -1 <= e_rc e <= e_cap e /\
  e_pp e <> 0 /\ e_pod e <> 0 /\ e_out e <> 0 /\ e_first e <> 0 /\
  e_pod e mod 16 = 0 /\ amem_range (e_pod e) (e_len e + 8) /\
  0 < e_src e /\ e_src e + e_left e <= 2 ^ 63 /\ amem_range (e_src e) (e_left e) /\
  (forall a, e_src e <= a < e_src e + e_left e ->
   ~ (e_R e - T_SEG_STK <= a < e_R e) /\ ~ hd_inw e (hi_w1 I) a /\ ~ (e_pp e <= a < e_pp e + Layout.PP_SIZE)).

(* The memory-dependent conjuncts at mem_seg_of sh, one checker each. *)
Definition fsh_at (sh : list Z) : bool :=
  bytes_chk (aview Img0.rsegs H_w (mem_seg_of sh)) (shadow_addr (e_F env_seg)) sh.
Definition globs_at (sh : list Z) : bool :=
  ranges_chk (aview Img0.rsegs H_w (mem_seg_of sh)) (fun a => a) (hi_globs headamp_himg_A).
Definition rz_at (sh : list Z) : bool :=
  ranges_chk (aview Img0.rsegs H_w (mem_seg_of sh)) (fun o => e_R env_seg + o) (hi_rz headamp_himg_A).
Definition strs_at (sh : list Z) : bool := strs_chk H_w (mem_seg_of sh) (hi_strs headamp_himg_A).
Definition cells_at (sh : list Z) : bool :=
  cells_chk Img0.rsegs (mrestrict H_w (mem_seg_of sh)) (hi_cells headamp_himg_A).
Definition guard_at (sh : list Z) : bool :=
  guard_chk (aview Img0.rsegs H_w (mem_seg_of sh)) (hi_gotw headamp_himg_A) (hi_guard headamp_himg_A).
Definition cuts_at (sh : list Z) : bool :=
  cut_chk H_w (mem_seg_of sh) regs1_seg env_seg (hi_L1 headamp_himg_A) &&
  cut_chk H_w (mem_seg_of sh) regs2_seg env_seg (hi_L2 headamp_himg_A) &&
  cut_chk H_w (mem_seg_of sh) regs3_seg env_seg (hi_L3 headamp_himg_A) &&
  cut_chk H_w (mem_seg_of sh) regs4_seg env_seg (hi_L4 headamp_himg_A) &&
  cut_chk H_w (mem_seg_of sh) regs5_seg env_seg (hi_L5 headamp_himg_A) &&
  cut_chk H_w (mem_seg_of sh) regs6_seg env_seg (hi_L6 headamp_himg_A) &&
  cut_chk H_w (mem_seg_of sh) regs7_seg env_seg (hi_L7 headamp_himg_A) &&
  cut_chk H_w (mem_seg_of sh) regs8_seg env_seg (hi_L8 headamp_himg_A) &&
  cut_chk H_w (mem_seg_of sh) regs9_seg env_seg (hi_L9 headamp_himg_A).

(* At any pattern sh whose seven checks pass, (H_w, mem_seg_of sh, regs1_seg .. regs9_seg, env_seg) is the state. *)
Lemma seg_static_of : forall sh,
  fsh_at sh = true -> globs_at sh = true -> rz_at sh = true -> strs_at sh = true ->
  cells_at sh = true -> guard_at sh = true -> cuts_at sh = true ->
  hd_seg_static Img0.rsegs headamp_himg_A sh 0x9bc80 0x9d068.
Proof.
intros sh F G Z S C U K.
unfold fsh_at, globs_at, rz_at, strs_at, cells_at, guard_at, cuts_at in *.
rewrite !andb_true_iff in K. destruct K as [[[[[[[[K1 K2] K3] K4] K5] K6] K7] K8] K9].
unfold hd_seg_static.
exists H_w, (mem_seg_of sh), regs1_seg, regs2_seg, regs3_seg, regs4_seg, regs5_seg, regs6_seg, regs7_seg,
  regs8_seg, regs9_seg, env_seg.
split; [unfold hd_fsh; exact (bytes_chk_ok _ _ _ F)|].
split; [exact (ranges_chk_ok _ _ _ G)|].
split; [exact (ranges_chk_ok _ _ _ Z)|].
split; [exact (strs_chk_ok _ _ _ S)|].
split; [unfold hd_ro_cells; exact (cells_chk_ok _ _ _ C)|].
split; [exact (aro_A sh)|].
split; [exact (guard_chk_ok _ _ _ U)|].
split; [exact (rom_A sh)|].
split; [exact (cut_chk_ok _ _ _ _ _ K1)|]. split; [exact (cut_chk_ok _ _ _ _ _ K2)|].
split; [exact (cut_chk_ok _ _ _ _ _ K3)|]. split; [exact (cut_chk_ok _ _ _ _ _ K4)|].
split; [exact (cut_chk_ok _ _ _ _ _ K5)|]. split; [exact (cut_chk_ok _ _ _ _ _ K6)|].
split; [exact (cut_chk_ok _ _ _ _ _ K7)|]. split; [exact (cut_chk_ok _ _ _ _ _ K8)|].
split; [exact (cut_chk_ok _ _ _ _ _ K9)|].
split; [exact sp_A|].
destruct env_A as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14).
split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
split; [exact E6|]. split; [exact E7|]. split; [exact E8|]. split; [exact E9|]. split; [exact E10|].
split; [exact E11|]. split; [exact E12|]. split; [exact E13|]. split; [exact E14|].
exact src_apart_A.
Qed.

(* After the prologue (the shadow pattern of C1 .. C5, which headamp_build_contract, headamp_dup_contract and
   headamp_check_contract take in hd_seg_pre). *)
Lemma fsh_at_A : fsh_at (hi_shA headamp_himg_A) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma globs_at_A : globs_at (hi_shA headamp_himg_A) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rz_at_A : rz_at (hi_shA headamp_himg_A) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma strs_at_A : strs_at (hi_shA headamp_himg_A) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cells_at_A : cells_at (hi_shA headamp_himg_A) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma guard_at_A : guard_at (hi_shA headamp_himg_A) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cuts_at_A : cuts_at (hi_shA headamp_himg_A) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma headamp_seg_static_A : hd_seg_static Img0.rsegs headamp_himg_A (hi_shA headamp_himg_A) 0x9bc80 0x9d068.
Proof. exact (seg_static_of _ fsh_at_A globs_at_A rz_at_A strs_at_A cells_at_A guard_at_A cuts_at_A). Qed.
Print Assumptions headamp_seg_static_A.

(* With the res granules 0x30 and 0x31 in scope (0x00 and 0x04: the shadow pattern of C6 .. C9, which
   headamp_first_contract and headamp_plain_contract take in hd_seg_pre): the same state, with mem_segB. *)
Lemma fsh_at_B : fsh_at (hi_shB headamp_himg_A) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma globs_at_B : globs_at (hi_shB headamp_himg_A) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rz_at_B : rz_at (hi_shB headamp_himg_A) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma strs_at_B : strs_at (hi_shB headamp_himg_A) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cells_at_B : cells_at (hi_shB headamp_himg_A) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma guard_at_B : guard_at (hi_shB headamp_himg_A) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cuts_at_B : cuts_at (hi_shB headamp_himg_A) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma headamp_seg_static_A_shB : hd_seg_static Img0.rsegs headamp_himg_A (hi_shB headamp_himg_A) 0x9bc80 0x9d068.
Proof. exact (seg_static_of _ fsh_at_B globs_at_B rz_at_B strs_at_B cells_at_B guard_at_B cuts_at_B). Qed.
Print Assumptions headamp_seg_static_A_shB.

(* mem_segB differs from mem_seg at the two shadow bytes of the res granules only. *)
Lemma headamp_seg_shB_A : forall w, bv_unsigned w <> shadow_addr (e_F env_seg) + 0x30 ->
  bv_unsigned w <> shadow_addr (e_F env_seg) + 0x31 -> mem_segB w = mem_seg w.
Proof.
intros w H30 H31. unfold mem_segB, mem_seg, mem_seg_of.
destruct (bv_unsigned w <? SHADOW_OFF); [reflexivity|].
destruct (span_shadow (bv_unsigned w)); [reflexivity|].
f_equal. unfold byte_seg.
destruct ((shadow_addr (e_F env_seg) <=? bv_unsigned w) &&
          (bv_unsigned w <? shadow_addr (e_F env_seg) + Z.of_nat (length (hi_shA headamp_himg_A)))) eqn:EA.
- assert (Hl : length (hi_shB headamp_himg_A) = length (hi_shA headamp_himg_A)) by reflexivity.
  rewrite Hl, EA. f_equal.
  apply andb_prop in EA. destruct EA as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  change (length (hi_shA headamp_himg_A)) with 80%nat in E2. change (Z.of_nat 80) with 80 in E2.
  set (i := Z.to_nat (bv_unsigned w - shadow_addr (e_F env_seg))).
  assert (Hi : (i < 80)%nat) by (subst i; lia).
  assert (H48 : i <> 48%nat) by (subst i; lia).
  assert (H49 : i <> 49%nat) by (subst i; lia).
  clearbody i. clear - Hi H48 H49.
  do 80 (destruct i as [|i]; [reflexivity || (exfalso; lia)|]). lia.
- assert (Hl : length (hi_shB headamp_himg_A) = length (hi_shA headamp_himg_A)) by reflexivity.
  rewrite Hl, EA. reflexivity.
Qed.
Print Assumptions headamp_seg_shB_A.
