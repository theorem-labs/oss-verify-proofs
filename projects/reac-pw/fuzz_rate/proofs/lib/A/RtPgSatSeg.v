(* Image A's witness for the image-level premises of reac-pw/fuzz_rate's segment contracts (lib/A/RtPgCSpec.v
   rt_seg_pre, the frame-shadow premise and the cut lists hi_L1, hi_L3, hi_L6) at I = rate_himg_A (lib/A/RtPgImgA.v):
   rt_seg_static_A for M01 and M02 (the prologue's frame shadow), rt_seg_static_A_csv for M03 (M02's).
   At one concrete state over image A's loaded segments, the frame's shadow bytes, the 57 registered globals, the
   checked real-frame range, the 46 strings, the 43 read-only cells, the four tables, the read-only data, the
   read-only segments and the live values at C1, C3 and C6 hold together, so those premises are not vacuous on
   image A. Each shadow byte the witness memory holds is the one the runtime writes, and each program byte is read
   from the image.
   Pinned image: fuzz_rate.asan, sha256 22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a.
   Items 11 and 12 add RtPgCSpec.rt_img_facts at image A: rt_img_facts_wit_A (its per-state globals' shadow at both
   witness memories; the read ranges are loaded program data), rate_A_img_static (the image side of
   rt_static_of_img_facts, by computation) and the bridges rate_A_static_of_facts / rate_A_static_full to the main
   walk's chaining law.
   proves no function (kind: statement text) *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YP09 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YO0f YG00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgImgA RtPgSat.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* The application spans whose shadow bytes the witness memory holds. Each registered global's
   [beg, beg + size_with_redzone) lies in one of them, and the first holds every string's 64-byte blocks (the shadow
   hulls rt_cstr reads). *)
Definition seg_spans : list (Z * Z) := [(0x20f80, 0x21740); (0x9bac0, 0x9bd00)].

Definition gdummy : Z * (Z * Z * Z) := (0, (0, 0, 0)).
(* The 57 rows, measured with RtPgSat.v's checkers: each descriptor's beg, size and size_with_redzone are the
   image's (globals_chk, rate_A_globals_chk); their ranges [beg, beg + size_with_redzone) are ascending and apart
   (so each granule has at most one global's shadow byte) and lie in seg_spans; each string of hi_strs is in the
   image with its NUL and is the global with beg = its address and size = its length + 1 (cstrs_img_chk). *)
Lemma rate_A_globals_seg_chk :
  forallb (fun k => let '(_, (b1, _, r1)) := nth k rate_A_globals gdummy in
                    let '(_, (b2, _, _)) := nth (S k) rate_A_globals gdummy in b1 + r1 <=? b2) (seq 0 56) &&
  forallb (fun g => let '(_, (b, _, r)) := g in existsb (fun s => (fst s <=? b) && (b + r <=? snd s)) seg_spans)
    rate_A_globals &&
  cstrs_img_chk segsA rate_A_globals (hi_strs rate_himg_A) = true.
Proof. vm_compute. reflexivity. Qed.
(* They are the rows of hi_globs (address, size). *)
Lemma rate_A_globals_globs :
  map (fun g => let '(_, (b, n, _)) := g in (b, n)) rate_A_globals = hi_globs rate_himg_A.
Proof. vm_compute. reflexivity. Qed.

(* ======================================== the run's quantities ======================================== *)
(* S the entry sp (a user stack address); R = (S - 0x1e0) & -32; F a class-3 side-stack frame (512 bytes,
   512-aligned); the pp, pod and buf blocks (16-aligned) and the input elsewhere in user memory. The seven header
   values are in their ranges (rt_hdr_ok). *)
Definition env_seg : rt_renv := {|
  q_S := 0x7fffffff0000; q_R := 0x7ffffffefe20; q_F := 0x7ff000000000;
  q_pp := 0x7e0000000010; q_pod := 0x7e0000010010; q_buf := 0x7e0000020010; q_len := 16;
  q_fl := 1; q_mask := 7; q_buflen := 23; q_b3 := 255; q_b4 := 255; q_b5 := 255; q_b6 := 255;
  q_src := 0x7d0000000001; q_left := 16 |}.

Definition rng_apartb (r1 r2 : Z * Z) : bool := (fst r1 + snd r1 <=? fst r2) || (fst r2 + snd r2 <=? fst r1).
Fixpoint all_apartb (l : list (Z * Z)) : bool :=
  match l with [] => true | r :: t => forallb (rng_apartb r) t && all_apartb t end.
(* The real frame [R, S), F's frame, the pp, pod and buf blocks and the input (start, length). *)
Definition env_ranges (e : rt_renv) : list (Z * Z) :=
  [(q_R e, q_S e - q_R e); (q_F e, YG00.fs_frame_bytes (hi_cid rate_himg_A)); (q_pp e, Layout.PP_SIZE);
   (q_pod e, q_len e); (q_buf e, rt_bl (q_buflen e)); (q_src e, q_left e)].
(* The choice: R = (S - 0x1e0) & -32 (the prologue's s1), F 512-aligned, pp, pod and buf 16-aligned; the six ranges
   lie above the image (kImgEnd) and below kHighMemEnd, pairwise apart; the header values are in range. *)
Lemma env_seg_chk :
  (q_R env_seg =? Z.land (q_S env_seg - hi_rsz rate_himg_A) (-32)) && (q_F env_seg mod 512 =? 0) &&
  (q_pp env_seg mod 16 =? 0) && (q_pod env_seg mod 16 =? 0) && (q_buf env_seg mod 16 =? 0) &&
  forallb (fun r => (kImgEnd <=? fst r) && (fst r + snd r <=? kHighMemEnd)) (env_ranges env_seg) &&
  all_apartb (env_ranges env_seg) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma env_seg_hdr : rt_hdr_ok env_seg.
Proof. unfold rt_hdr_ok. cbn [q_fl q_mask q_buflen q_b3 q_b4 q_b5 q_b6 env_seg]. lia. Qed.

(* ================================================ the witness ================================================ *)
(* The real-frame cells (address, 8-byte value) that a cut list L names, at e. *)
Definition cut_cells (e : rt_renv) (L : list (rt_loc * rt_x)) : list (Z * Z) :=
  flat_map (fun f => match fst f with
                     | LCell b o => [(rt_xv e b + o, rt_xv e (snd f) mod 2 ^ 64)]
                     | LReg _ => []
                     end) L.
Definition cells_seg : list (Z * Z) :=
  cut_cells env_seg (hi_L1 rate_himg_A ++ hi_L3 rate_himg_A ++ hi_L6 rate_himg_A).

(* The byte at u >= SHADOW_OFF, for a frame-shadow pattern pat: the shadow byte of a granule in seg_spans (RtPgSat.granule_shadow over the 57
   globals: 0 for a full granule, size mod 8 for the last partial one, 0xf9 for a redzone one, and the 0 of the
   freshly mapped shadow for the three gaps no global covers, as RtPgSat.v's mem_w); the frame's shadow bytes pat from
   shadow_addr F; 0 for the shadow bytes of the real-frame ranges hi_rz; the bytes of the cells of hi_L1, hi_L3 and
   hi_L6; else none. *)
Definition byte_segp (pat : list Z) (u : Z) : option Z :=
  if existsb (fun r => (shadow_addr (fst r) <=? u) && (u <? shadow_addr (snd r))) seg_spans
  then Some (granule_shadow rate_A_globals ((u - SHADOW_OFF) * 8))
  else if (shadow_addr (q_F env_seg) <=? u) &&
          (u <? shadow_addr (q_F env_seg) + Z.of_nat (length pat))
  then Some (nth (Z.to_nat (u - shadow_addr (q_F env_seg))) pat 0)
  else if existsb (fun z => (shadow_addr (q_R env_seg + fst z) <=? u) &&
                            (u <=? shadow_addr (q_R env_seg + fst z + snd z - 1))) (hi_rz rate_himg_A)
  then Some 0
  else match find (fun c => (fst c <=? u) && (u <? fst c + 8)) cells_seg with
       | Some c => Some (YO0f.le_byte (snd c) 8 (Z.to_nat (u - fst c)))
       | None => None
       end.
(* The witness memory: nothing below SHADOW_OFF (so no byte of the image, and every program byte is read through
   mbyte's fall-back to seg_rom), byte_seg above. No byte is hidden (RtPgSat.H_w). *)
Definition mem_segp (pat : list Z) : word -> option byte := fun w =>
  if bv_unsigned w <? SHADOW_OFF then None else option_map (fun v => Z_to_bv 8 v) (byte_segp pat (bv_unsigned w)).
(* With the prologue's frame shadow (C1, C3), and with M02's (C6). *)
Definition mem_seg : word -> option byte := mem_segp (hi_shA rate_himg_A).
Definition mem_segB : word -> option byte := mem_segp (hi_shB rate_himg_A).

(* The register map at a cut: each register L names holds the value L gives at e, and sp holds R. *)
Definition cut_regs (e : rt_renv) (L : list (rt_loc * rt_x)) : bvmap 5 word :=
  fold_right (fun f m => match fst f with
                         | LReg r => regupd m (Z_to_bv 5 r) (Z_to_bv 64 (rt_xv e (snd f)))
                         | LCell _ _ => m
                         end)
    (regupd bvmap_empty (Z_to_bv 5 2) (Z_to_bv 64 (q_R e))) L.
Definition regs1_seg : bvmap 5 word := cut_regs env_seg (hi_L1 rate_himg_A).
Definition regs3_seg : bvmap 5 word := cut_regs env_seg (hi_L3 rate_himg_A).
Definition regs6_seg : bvmap 5 word := cut_regs env_seg (hi_L6 rate_himg_A).

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

(* rt_cstr for each string of a list. *)
Definition strs_chk (h : word -> bool) (mem : word -> option byte) (l : list (Z * list Z)) : bool :=
  forallb (fun c => cstr_chk segsA h mem (fst c) (snd c)) l.
Lemma strs_chk_ok : forall h mem l, strs_chk h mem l = true -> Forall (fun s => rt_cstr segsA h mem (fst s) (snd s)) l.
Proof.
intros h mem l H. apply Forall_forall. intros c Hc. cbv beta. apply cstr_chk_ok.
unfold strs_chk in H. rewrite forallb_forall in H. exact (H c Hc).
Qed.

(* rt_i32tab / rt_u64tab for each table of a list. *)
Definition i32s_chk (h : word -> bool) (mem : word -> option byte) (l : list (Z * list Z)) : bool :=
  forallb (fun t => i32tab_chk segsA h mem (fst t) (snd t)) l.
Lemma i32s_chk_ok : forall h mem l, i32s_chk h mem l = true -> Forall (fun t => rt_i32tab segsA h mem (fst t) (snd t)) l.
Proof.
intros h mem l H. apply Forall_forall. intros t Ht. cbv beta. apply i32tab_chk_ok.
unfold i32s_chk in H. rewrite forallb_forall in H. exact (H t Ht).
Qed.
Definition u64s_chk (h : word -> bool) (mem : word -> option byte) (l : list (Z * list Z)) : bool :=
  forallb (fun t => u64tab_chk segsA h mem (fst t) (snd t)) l.
Lemma u64s_chk_ok : forall h mem l, u64s_chk h mem l = true -> Forall (fun t => rt_u64tab segsA h mem (fst t) (snd t)) l.
Proof.
intros h mem l H. apply Forall_forall. intros t Ht. cbv beta. apply u64tab_chk_ok.
unfold u64s_chk in H. rewrite forallb_forall in H. exact (H t Ht).
Qed.

(* RtPgBase.rt_at and rt_cut. *)
Definition at_chk (h : word -> bool) (mem : word -> option byte) (regs : bvmap 5 word) (e : rt_renv)
  (l : rt_loc) (v : Z) : bool :=
  match l with
  | LReg r => bv_unsigned (getr regs (Z_to_bv 5 r)) =? bv_unsigned (Z_to_bv 64 v)
  | LCell b o => val_chk segsA (mrestrict h mem) (rt_xv e b + o) 8 (v mod 2 ^ 64)
  end.
Lemma at_chk_ok : forall h mem regs e l v, at_chk h mem regs e l v = true -> rt_at segsA h mem regs e l v.
Proof.
intros h mem regs e [r|b o] v E; unfold at_chk in E; unfold rt_at.
- apply bv_eq. apply Z.eqb_eq. exact E.
- apply val_chk_ok. exact E.
Qed.
Definition cut_chk (h : word -> bool) (mem : word -> option byte) (regs : bvmap 5 word) (e : rt_renv)
  (L : list (rt_loc * rt_x)) : bool :=
  forallb (fun f => at_chk h mem regs e (fst f) (rt_xv e (snd f))) L.
Lemma cut_chk_ok : forall h mem regs e L, cut_chk h mem regs e L = true -> rt_cut segsA h mem regs e L.
Proof.
intros h mem regs e L H. unfold rt_cut. apply Forall_forall. intros f Hf. cbv beta. apply at_chk_ok.
unfold cut_chk in H. rewrite forallb_forall in H. exact (H f Hf).
Qed.

(* Every loaded segment ends at or below kImgEnd (< SHADOW_OFF). *)
Definition segsA_end_chk : bool := forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? kImgEnd) segsA.
Lemma segsA_end_chk_ok : segsA_end_chk = true.
Proof. vm_compute. reflexivity. Qed.
Lemma segsA_end : forall s, In s segsA -> Z.of_N (seg_base s) + Z.of_N (seg_size s) <= kImgEnd.
Proof.
intros s Hs. pose proof segsA_end_chk_ok as E. unfold segsA_end_chk in E. rewrite forallb_forall in E.
apply Z.leb_le. exact (E s Hs).
Qed.

(* Below SHADOW_OFF the witness reads the image. *)
Lemma mem_segp_low : forall pat a, 0 <= a < SHADOW_OFF -> mem_segp pat (Z_to_bv 64 a) = None.
Proof.
intros pat a Ha. unfold mem_segp.
assert (Hu : bv_unsigned (Z_to_bv 64 a) = a).
{ rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). unfold SHADOW_OFF in Ha. lia. }
assert (Hlt : (a <? SHADOW_OFF) = true) by (apply Z.ltb_lt; lia).
rewrite Hu, Hlt. reflexivity.
Qed.
Lemma aview_lowp : forall pat a, 0 <= a < SHADOW_OFF ->
  aview segsA H_w (mem_segp pat) a = option_map (fun b : byte => bv_unsigned b) (seg_rom segsA (Z_to_bv 64 a)).
Proof. intros pat a Ha. unfold aview, mbyte, mrestrict, H_w. rewrite (mem_segp_low pat a Ha). reflexivity. Qed.
Lemma aview_low : forall a, 0 <= a < SHADOW_OFF ->
  aview segsA H_w mem_seg a = option_map (fun b : byte => bv_unsigned b) (seg_rom segsA (Z_to_bv 64 a)).
Proof. exact (aview_lowp (hi_shA rate_himg_A)). Qed.

(* ============================== the conjuncts at the witness, one by one ============================== *)
(* 1. The frame's shadow bytes after the prologue. *)
Lemma fsh_A_chk : bytes_chk (aview segsA H_w mem_seg) (shadow_addr (q_F env_seg)) (hi_shA rate_himg_A) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma fsh_A : rt_fsh segsA H_w mem_seg (q_F env_seg) (hi_shA rate_himg_A).
Proof. unfold rt_fsh. exact (bytes_chk_ok _ _ _ fsh_A_chk). Qed.

(* 2. The 57 registered globals. *)
Lemma globs_A_chk : ranges_chk (aview segsA H_w mem_seg) (fun a => a) (hi_globs rate_himg_A) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma globs_A :
  Forall (fun g => range_addressable (aview segsA H_w mem_seg) SHADOW_OFF (fst g) (snd g)) (hi_globs rate_himg_A).
Proof. exact (ranges_chk_ok _ _ _ globs_A_chk). Qed.

(* 3. The real-frame ranges the code shadow-checks. *)
Lemma rz_A_chk : ranges_chk (aview segsA H_w mem_seg) (fun o => q_R env_seg + o) (hi_rz rate_himg_A) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rz_A :
  Forall (fun z => range_addressable (aview segsA H_w mem_seg) SHADOW_OFF (q_R env_seg + fst z) (snd z))
    (hi_rz rate_himg_A).
Proof. exact (ranges_chk_ok _ _ _ rz_A_chk). Qed.

(* 4. The 46 strings. *)
Lemma strs_A_chk : strs_chk H_w mem_seg (hi_strs rate_himg_A) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma strs_A : Forall (fun s => rt_cstr segsA H_w mem_seg (fst s) (snd s)) (hi_strs rate_himg_A).
Proof. exact (strs_chk_ok _ _ _ strs_A_chk). Qed.

(* 5. The read-only cells. *)
Lemma cells_A_chk : cells_chk segsA (mrestrict H_w mem_seg) (hi_cells rate_himg_A) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cells_A : rt_ro_cells segsA H_w mem_seg (hi_cells rate_himg_A).
Proof. unfold rt_ro_cells. exact (cells_chk_ok _ _ _ cells_A_chk). Qed.

(* 6. The four tables. *)
Lemma i32_A_chk : i32s_chk H_w mem_seg (hi_i32 rate_himg_A) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma i32_A : Forall (fun t => rt_i32tab segsA H_w mem_seg (fst t) (snd t)) (hi_i32 rate_himg_A).
Proof. exact (i32s_chk_ok _ _ _ i32_A_chk). Qed.
Lemma u64_A_chk : u64s_chk H_w mem_seg (hi_u64 rate_himg_A) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma u64_A : Forall (fun t => rt_u64tab segsA H_w mem_seg (fst t) (snd t)) (hi_u64 rate_himg_A).
Proof. exact (u64s_chk_ok _ _ _ u64_A_chk). Qed.

(* 7. The read-only data, for every symbol record B: RO_LO = 0x9b6e0 and RO_HI = 0x9cb68 (and every read-only
   segment) lie below SHADOW_OFF. *)
Lemma aro_A : forall B : asyms, arodata_okP segsA 0x9b6e0 0x9cb68 B (aview segsA H_w mem_seg).
Proof.
intros B a Hro _ _. apply aview_low. hnf in Hro. destruct Hro as [(s & Hs & _ & Hr) | Hr].
- pose proof (segsA_end s Hs) as Hb. pose proof (N2Z.is_nonneg (seg_base s)) as H0.
  unfold kImgEnd in Hb. unfold SHADOW_OFF. lia.
- unfold SHADOW_OFF. lia.
Qed.

(* 8. The live values at C1 (regs1_seg), at C3 (regs3_seg, a0 = pod) and at C6 (regs6_seg, a0 = buf), over the same
   memory. *)
Lemma cut1_A_chk : cut_chk H_w mem_seg regs1_seg env_seg (hi_L1 rate_himg_A) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cut1_A : rt_cut segsA H_w mem_seg regs1_seg env_seg (hi_L1 rate_himg_A).
Proof. exact (cut_chk_ok _ _ _ _ _ cut1_A_chk). Qed.
Lemma cut3_A_chk : cut_chk H_w mem_seg regs3_seg env_seg (hi_L3 rate_himg_A) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cut3_A : rt_cut segsA H_w mem_seg regs3_seg env_seg (hi_L3 rate_himg_A).
Proof. exact (cut_chk_ok _ _ _ _ _ cut3_A_chk). Qed.
Lemma cut6_A_chk : cut_chk H_w mem_seg regs6_seg env_seg (hi_L6 rate_himg_A) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cut6_A : rt_cut segsA H_w mem_seg regs6_seg env_seg (hi_L6 rate_himg_A).
Proof. exact (cut_chk_ok _ _ _ _ _ cut6_A_chk). Qed.

(* 9. The run's quantities. *)
Lemma env_A : rt_hdr_ok env_seg /\ q_pp env_seg <> 0 /\ q_pod env_seg <> 0 /\ q_buf env_seg <> 0 /\
  q_R env_seg mod 16 = 0 /\ q_R env_seg + hi_rsz rate_himg_A <= q_S env_seg.
Proof.
split; [exact env_seg_hdr|].
split; [apply Z.eqb_neq; vm_compute; reflexivity|].
split; [apply Z.eqb_neq; vm_compute; reflexivity|].
split; [apply Z.eqb_neq; vm_compute; reflexivity|].
split; [apply Z.eqb_eq; vm_compute; reflexivity|].
apply Z.leb_le. vm_compute. reflexivity.
Qed.

(* 10. Every byte of a read-only segment reads as the image's, at every world whose hidden set is H_w. *)
Lemma rom_A : forall W : world segsA, w_H W = H_w -> rom_view segsA W mem_seg.
Proof.
intros W HW a Ha. rewrite HW. apply aview_low. hnf in Ha. destruct Ha as (s & Hs & _ & Hr).
pose proof (segsA_end s Hs) as Hb. pose proof (N2Z.is_nonneg (seg_base s)) as H0.
unfold kImgEnd in Hb. unfold SHADOW_OFF. lia.
Qed.

(* ================================================ the lemma ================================================ *)
(* The image-level conjuncts of rt_seg_pre at I = rate_himg_A (RLO = 0x9b6e0, RHI = 0x9cb68), the frame-shadow
   premise and the three start cut lists hi_L1, hi_L3 and hi_L6 hold together at one state
   (H, mem, regs1, regs3, regs6, e). *)
Lemma rt_seg_static_A : exists (H : word -> bool) (mem : word -> option byte)
  (regs1 regs3 regs6 : bvmap 5 word) (e : rt_renv),
  rt_fsh segsA H mem (q_F e) (hi_shA rate_himg_A) /\
  Forall (fun g => range_addressable (aview segsA H mem) SHADOW_OFF (fst g) (snd g)) (hi_globs rate_himg_A) /\
  Forall (fun z => range_addressable (aview segsA H mem) SHADOW_OFF (q_R e + fst z) (snd z)) (hi_rz rate_himg_A) /\
  Forall (fun s => rt_cstr segsA H mem (fst s) (snd s)) (hi_strs rate_himg_A) /\
  rt_ro_cells segsA H mem (hi_cells rate_himg_A) /\
  Forall (fun t => rt_i32tab segsA H mem (fst t) (snd t)) (hi_i32 rate_himg_A) /\
  Forall (fun t => rt_u64tab segsA H mem (fst t) (snd t)) (hi_u64 rate_himg_A) /\
  (forall B : asyms, arodata_okP segsA 0x9b6e0 0x9cb68 B (aview segsA H mem)) /\
  rt_cut segsA H mem regs1 e (hi_L1 rate_himg_A) /\
  rt_cut segsA H mem regs3 e (hi_L3 rate_himg_A) /\
  rt_cut segsA H mem regs6 e (hi_L6 rate_himg_A) /\
  rt_hdr_ok e /\ q_pp e <> 0 /\ q_pod e <> 0 /\ q_buf e <> 0 /\
  q_R e mod 16 = 0 /\ q_R e + hi_rsz rate_himg_A <= q_S e /\
  (forall W : world segsA, w_H W = H -> rom_view segsA W mem).
Proof.
exists H_w, mem_seg, regs1_seg, regs3_seg, regs6_seg, env_seg.
split; [exact fsh_A|].
split; [exact globs_A|].
split; [exact rz_A|].
split; [exact strs_A|].
split; [exact cells_A|].
split; [exact i32_A|].
split; [exact u64_A|].
split; [exact aro_A|].
split; [exact cut1_A|].
split; [exact cut3_A|].
split; [exact cut6_A|].
destruct env_A as (E1 & E2 & E3 & E4 & E5 & E6).
split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|].
split; [exact E5|]. split; [exact E6|].
exact rom_A.
Qed.
Print Assumptions rt_seg_static_A.

(* ===================== the csv segment's start: M02's frame shadow with the C6 values ===================== *)
(* rate_csv_contract asks rt_fsh hi_shB (not hi_shA) together with hi_L6: the same image-level conjuncts hold at the
   witness memory whose frame shadow is M02's (granules 48, 50, 52 = 0x04). *)
Lemma fshB_A_chk : bytes_chk (aview segsA H_w mem_segB) (shadow_addr (q_F env_seg)) (hi_shB rate_himg_A) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma globsB_A_chk : ranges_chk (aview segsA H_w mem_segB) (fun a => a) (hi_globs rate_himg_A) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rzB_A_chk : ranges_chk (aview segsA H_w mem_segB) (fun o => q_R env_seg + o) (hi_rz rate_himg_A) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma strsB_A_chk : strs_chk H_w mem_segB (hi_strs rate_himg_A) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cellsB_A_chk : cells_chk segsA (mrestrict H_w mem_segB) (hi_cells rate_himg_A) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma i32B_A_chk : i32s_chk H_w mem_segB (hi_i32 rate_himg_A) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma u64B_A_chk : u64s_chk H_w mem_segB (hi_u64 rate_himg_A) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cut6B_A_chk : cut_chk H_w mem_segB regs6_seg env_seg (hi_L6 rate_himg_A) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rt_seg_static_A_csv : exists (H : word -> bool) (mem : word -> option byte) (regs6 : bvmap 5 word) (e : rt_renv),
  rt_fsh segsA H mem (q_F e) (hi_shB rate_himg_A) /\
  Forall (fun g => range_addressable (aview segsA H mem) SHADOW_OFF (fst g) (snd g)) (hi_globs rate_himg_A) /\
  Forall (fun z => range_addressable (aview segsA H mem) SHADOW_OFF (q_R e + fst z) (snd z)) (hi_rz rate_himg_A) /\
  Forall (fun s => rt_cstr segsA H mem (fst s) (snd s)) (hi_strs rate_himg_A) /\
  rt_ro_cells segsA H mem (hi_cells rate_himg_A) /\
  Forall (fun t => rt_i32tab segsA H mem (fst t) (snd t)) (hi_i32 rate_himg_A) /\
  Forall (fun t => rt_u64tab segsA H mem (fst t) (snd t)) (hi_u64 rate_himg_A) /\
  (forall B : asyms, arodata_okP segsA 0x9b6e0 0x9cb68 B (aview segsA H mem)) /\
  rt_cut segsA H mem regs6 e (hi_L6 rate_himg_A) /\
  rt_hdr_ok e /\ q_pp e <> 0 /\ q_buf e <> 0 /\
  q_R e mod 16 = 0 /\ q_R e + hi_rsz rate_himg_A <= q_S e /\
  (forall W : world segsA, w_H W = H -> rom_view segsA W mem).
Proof.
exists H_w, mem_segB, regs6_seg, env_seg.
split; [unfold rt_fsh; exact (bytes_chk_ok _ _ _ fshB_A_chk)|].
split; [exact (ranges_chk_ok _ _ _ globsB_A_chk)|].
split; [exact (ranges_chk_ok _ _ _ rzB_A_chk)|].
split; [exact (strs_chk_ok _ _ _ strsB_A_chk)|].
split; [unfold rt_ro_cells; exact (cells_chk_ok _ _ _ cellsB_A_chk)|].
split; [exact (i32s_chk_ok _ _ _ i32B_A_chk)|].
split; [exact (u64s_chk_ok _ _ _ u64B_A_chk)|].
split.
{ intros B a Hro _ _. apply aview_lowp. hnf in Hro. destruct Hro as [(s & Hs & _ & Hr) | Hr].
  - pose proof (segsA_end s Hs) as Hb. pose proof (N2Z.is_nonneg (seg_base s)) as H0.
    unfold kImgEnd in Hb. unfold SHADOW_OFF. lia.
  - unfold SHADOW_OFF. lia. }
split; [exact (cut_chk_ok _ _ _ _ _ cut6B_A_chk)|].
destruct env_A as (E1 & E2 & _ & E4 & E5 & E6).
split; [exact E1|]. split; [exact E2|]. split; [exact E4|]. split; [exact E5|]. split; [exact E6|].
intros W HW a Ha. rewrite HW. apply aview_lowp. hnf in Ha. destruct Ha as (s & Hs & _ & Hr).
pose proof (segsA_end s Hs) as Hb. pose proof (N2Z.is_nonneg (seg_base s)) as H0.
unfold kImgEnd in Hb. unfold SHADOW_OFF. lia.
Qed.
Print Assumptions rt_seg_static_A_csv.

(* 11. RtPgCSpec.rt_img_facts at image A, the hypothesis the walks take to re-derive the string, table and cell
   facts after a call that lets runtime-owned bytes change. Its per-state part rt_globs_marked asks, in every AR
   state, block_shadow of each of the 57 globals of hi_globs: at both witness memories above, mem_seg (M01, M02) and
   mem_segB (M03), each global's shadow is the runtime's (0 for each full granule, the size mod 8 for a last partial
   one), so that conclusion holds where the segment starts are witnessed. Each range of rt_ro_ranges rate_himg_A (the
   read ranges whose bytes rt_img_facts keeps: no owned static) is non-empty and lies in the image's loaded
   segments, so it is program data, never shadow. The parts that are facts of the symbol record alone (which bytes
   are owned statics, which shadow cells and ranges AR fixes) need image A's record TfibB; image A's close proves
   rt_img_facts there by computation. *)
Definition bshadow_chk (rd : reader) (p n : Z) : bool :=
  (p mod 8 =? 0) && (0 <=? n) &&
  forallb (fun k => oz_eqb (rd (shadow_of_addr SHADOW_OFF p + Z.of_nat k)) (if Z.of_nat k <? n / 8 then 0 else n mod 8))
    (seq 0 (Z.to_nat ((n + 7) / 8))).
Lemma bshadow_chk_ok : forall rd p n, bshadow_chk rd p n = true -> block_shadow rd SHADOW_OFF p n.
Proof.
intros rd p n Hc. unfold bshadow_chk in Hc. rewrite !andb_true_iff in Hc. destruct Hc as [[H8 H0] Hk].
apply Z.eqb_eq in H8. apply Z.leb_le in H0.
split; [exact H8|]. split; [exact H0|]. intros i Hi.
assert (Hn : (Z.to_nat i < Z.to_nat ((n + 7) / 8))%nat) by lia.
pose proof (forallb_seq _ _ Hk _ Hn) as E. cbv beta in E. rewrite Z2Nat.id in E by lia.
exact (oz_eqb_ok _ _ E).
Qed.
Definition globs_bsh_chk (rd : reader) (l : list (Z * Z)) : bool := forallb (fun g => bshadow_chk rd (fst g) (snd g)) l.
Lemma globs_bsh_chk_ok : forall rd l, globs_bsh_chk rd l = true ->
  forall q sz, In (q, sz) l -> block_shadow rd SHADOW_OFF q sz.
Proof.
intros rd l H q sz Hin. apply bshadow_chk_ok. unfold globs_bsh_chk in H. rewrite forallb_forall in H.
exact (H (q, sz) Hin).
Qed.
Lemma globs_marked_A_chk :
  globs_bsh_chk (aview segsA H_w mem_seg) (hi_globs rate_himg_A) &&
  globs_bsh_chk (aview segsA H_w mem_segB) (hi_globs rate_himg_A) = true.
Proof. vm_compute. reflexivity. Qed.
Definition ro_ranges_img_chk : bool :=
  forallb (fun r => (0 <? snd r) && img_chk segsA (fst r) (Z.to_nat (snd r))) (rt_ro_ranges rate_himg_A).
Lemma ro_ranges_img_chk_ok : ro_ranges_img_chk = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rt_img_facts_wit_A :
  (forall q sz, In (q, sz) (hi_globs rate_himg_A) ->
     block_shadow (aview segsA H_w mem_seg) SHADOW_OFF q sz /\ block_shadow (aview segsA H_w mem_segB) SHADOW_OFF q sz) /\
  Forall (fun r => 0 < snd r /\ forall i, 0 <= i < snd r -> in_img segsA (fst r + i)) (rt_ro_ranges rate_himg_A).
Proof.
pose proof globs_marked_A_chk as E. apply andb_true_iff in E. destruct E as [E1 E2]. split.
- intros q sz Hin. split; [exact (globs_bsh_chk_ok _ _ E1 q sz Hin) | exact (globs_bsh_chk_ok _ _ E2 q sz Hin)].
- apply Forall_forall. intros r Hr. pose proof ro_ranges_img_chk_ok as R. unfold ro_ranges_img_chk in R.
  rewrite forallb_forall in R. specialize (R r Hr). cbv beta in R. apply andb_true_iff in R. destruct R as [R0 R1].
  apply Z.ltb_lt in R0. split; [exact R0|]. intros i Hi.
  exact (img_chk_ok segsA (fst r) (Z.to_nat (snd r)) R1 i ltac:(lia)).
Qed.
Print Assumptions rt_img_facts_wit_A.

(* 12. The image side of RtPgCSpec.rt_static_of_img_facts at image A (rt_img_static over [IMG_LO, IMG_TOP) and
   RO_LO / RO_HI = 0x9b6e0 / 0x9cb68), by computation over the loaded segments: each of the 46 strings is the image's
   bytes and NUL in a read-only segment, a registered global with room, 64 bytes inside the range; each of the 43
   cells, each entry of closed_list, ordered, switch.table.check_code and reac_rate_refuse_code.codes is the image's
   value in a read-only segment or [RO_LO, RO_HI). With it, rate_A_static_of_facts: at every AR state with the
   read-only data as in the image, image A's rt_img_facts gives rt_seg_pre's globals, strings, cells and tables. *)
Definition in_roPb (segs : list Segment) (rlo rhi a : Z) : bool :=
  existsb (fun sg => negb (seg_writable sg) && (Z.of_N (seg_base sg) <=? a) &&
                     (a <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) segs || ((rlo <=? a) && (a <? rhi)).
Lemma in_roPb_ok : forall segs rlo rhi a, in_roPb segs rlo rhi a = true -> in_roP segs rlo rhi a.
Proof.
intros segs rlo rhi a H. unfold in_roPb in H. apply orb_true_iff in H. unfold in_roP. destruct H as [H|H].
- left. apply existsb_exists in H. destruct H as (sg & Hin & Hb). rewrite !andb_true_iff in Hb.
  destruct Hb as [[Hw H1] H2]. apply negb_true_iff in Hw. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  exists sg. split; [exact Hin|]. split; [exact Hw | lia].
- right. apply andb_true_iff in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.
Definition img_bytes_ro_chk (rlo rhi a : Z) (l : list Z) : bool :=
  forallb (fun k => in_roPb segsA rlo rhi (a + Z.of_nat k) && oz_eqb (img_byte segsA (a + Z.of_nat k)) (nth k l 0))
    (seq 0 (length l)).
Lemma img_bytes_ro_chk_ok : forall rlo rhi a l, img_bytes_ro_chk rlo rhi a l = true -> rt_img_bytes segsA rlo rhi a l.
Proof.
intros rlo rhi a l Hc i Hi. unfold img_bytes_ro_chk in Hc. assert (Hk : (Z.to_nat i < length l)%nat) by lia.
pose proof (forallb_seq _ _ Hc _ Hk) as E. cbv beta in E. rewrite Z2Nat.id in E by lia.
apply andb_true_iff in E. destruct E as [E1 E2]. split; [exact (in_roPb_ok _ _ _ _ E1)|].
exact (oz_eqb_ok _ _ E2).
Qed.
Definition img_val_ro_chk (rlo rhi a : Z) (n : nat) (v : Z) : bool :=
  img_val_chk segsA a n v && forallb (fun k => in_roPb segsA rlo rhi (a + Z.of_nat k)) (seq 0 n).
Lemma img_val_ro_chk_ok : forall rlo rhi a n v, img_val_ro_chk rlo rhi a n v = true -> rt_img_val segsA rlo rhi a n v.
Proof.
intros rlo rhi a n v Hc k Hk. unfold img_val_ro_chk in Hc. apply andb_true_iff in Hc. destruct Hc as [C1 C2].
split; [exact (in_roPb_ok _ _ _ _ (forallb_seq _ _ C2 _ Hk)) | exact (img_val_chk_ok segsA a n v C1 k Hk)].
Qed.
Definition img_static_chk (I : rt_himg) (lo hi rlo rhi : Z) : bool :=
  forallb (fun s => img_bytes_ro_chk rlo rhi (fst s) (snd s ++ [0]) &&
     forallb (fun b => (0 <? b) && (b <? 256)) (snd s) && (0 <? fst s) &&
     (fst s + Z.of_nat (length (snd s)) + 1 <=? 2 ^ 63) && img_chk segsA (fst s) (length (snd s) + 1) &&
     amem_rangeb (fst s) (Z.of_nat (length (snd s)) + 1) &&
     existsb (fun g => (fst g =? fst s) && (Z.of_nat (length (snd s)) + 1 <=? snd g)) (hi_globs I) &&
     (lo + 64 <=? fst s) && (fst s + Z.of_nat (length (snd s)) + 1 + 64 <=? hi)) (hi_strs I) &&
  forallb (fun c => img_val_ro_chk rlo rhi (fst c) 8 (snd c)) (hi_cells I) &&
  forallb (fun t => img_chk segsA (fst t) (4 * length (snd t)) && (fst t mod 4 =? 0) &&
     forallb (fun k => img_val_ro_chk rlo rhi (fst t + 4 * Z.of_nat k) 4 (nth k (snd t) 0)) (seq 0 (length (snd t))) &&
     existsb (fun g => (fst g =? fst t) && (4 * Z.of_nat (length (snd t)) <=? snd g)) (hi_globs I)) (hi_i32 I) &&
  forallb (fun t => img_chk segsA (fst t) (8 * length (snd t)) && (fst t mod 8 =? 0) &&
     forallb (fun v => (0 <=? v) && (v <? 2 ^ 64)) (snd t) &&
     forallb (fun k => img_val_ro_chk rlo rhi (fst t + 8 * Z.of_nat k) 8 (nth k (snd t) 0)) (seq 0 (length (snd t))) &&
     existsb (fun g => (fst g =? fst t) && (8 * Z.of_nat (length (snd t)) <=? snd g)) (hi_globs I)) (hi_u64 I).
Lemma img_static_chk_ok : forall I lo hi rlo rhi, img_static_chk I lo hi rlo rhi = true ->
  rt_img_static segsA I lo hi rlo rhi.
Proof.
intros I lo hi rlo rhi H. unfold img_static_chk in H. rewrite !andb_true_iff in H. destruct H as [[[HS HC] HI] HU].
rewrite forallb_forall in HS, HC, HI, HU.
unfold rt_img_static. split; [|split; [|split]]; apply Forall_forall.
- intros (a, s) Hin. specialize (HS (a, s) Hin). cbv beta in HS. cbn [fst snd] in HS |- *.
  rewrite !andb_true_iff in HS. destruct HS as [[[[[[[[H1 H2] H3] H4] H5] H6] H7] H8] H9].
  split; [exact (img_bytes_ro_chk_ok _ _ _ _ H1)|].
  split; [exact (bytes_range_ok _ H2)|].
  split; [apply Z.ltb_lt; exact H3|].
  split; [apply Z.leb_le; exact H4|].
  split; [intros i Hi; apply (img_chk_ok segsA a (length s + 1) H5); lia|].
  split; [exact (amem_rangeb_ok _ _ H6)|].
  split; [exact (rt_glob_of_b a _ (hi_globs I) H7)|].
  split; [apply Z.leb_le; exact H8 | apply Z.leb_le; exact H9].
- intros (c, v) Hin. specialize (HC (c, v) Hin). cbv beta in HC. cbn [fst snd] in HC |- *.
  exact (img_val_ro_chk_ok _ _ _ _ _ HC).
- intros (t, vs) Hin. specialize (HI (t, vs) Hin). cbv beta in HI. cbn [fst snd] in HI |- *.
  rewrite !andb_true_iff in HI. destruct HI as [[[T1 T2] T3] T4].
  split; [intros i Hi; apply (img_chk_ok segsA t (4 * length vs) T1); lia|].
  split; [apply Z.eqb_eq; exact T2|].
  split; [|exact (rt_glob_of_b t _ (hi_globs I) T4)].
  intros i Hi. assert (Hk : (Z.to_nat i < length vs)%nat) by lia.
  pose proof (forallb_seq _ _ T3 _ Hk) as E. cbv beta in E. rewrite Z2Nat.id in E by lia.
  exact (img_val_ro_chk_ok _ _ _ _ _ E).
- intros (t, vs) Hin. specialize (HU (t, vs) Hin). cbv beta in HU. cbn [fst snd] in HU |- *.
  rewrite !andb_true_iff in HU. destruct HU as [[[[T1 T2] T3] T4] T5].
  split; [intros i Hi; apply (img_chk_ok segsA t (8 * length vs) T1); lia|].
  split; [apply Z.eqb_eq; exact T2|].
  split.
  { apply Forall_forall. intros v Hv. rewrite forallb_forall in T3. specialize (T3 v Hv). cbv beta in T3.
    apply andb_true_iff in T3. destruct T3 as [V1 V2]. apply Z.leb_le in V1. apply Z.ltb_lt in V2. lia. }
  split; [|exact (rt_glob_of_b t _ (hi_globs I) T5)].
  intros i Hi. assert (Hk : (Z.to_nat i < length vs)%nat) by lia.
  pose proof (forallb_seq _ _ T4 _ Hk) as E. cbv beta in E. rewrite Z2Nat.id in E by lia.
  exact (img_val_ro_chk_ok _ _ _ _ _ E).
Qed.
Lemma rate_A_img_static_chk : img_static_chk rate_himg_A IMG_LO IMG_TOP 0x9b6e0 0x9cb68 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rate_A_img_static : rt_img_static segsA rate_himg_A IMG_LO IMG_TOP 0x9b6e0 0x9cb68.
Proof. exact (img_static_chk_ok _ _ _ _ _ rate_A_img_static_chk). Qed.
Print Assumptions rate_A_img_static.
Section st. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma rate_A_static_of_facts : forall B : asyms, rt_img_facts segsA B rate_himg_A IMG_LO IMG_TOP ->
  forall ly S (W : world segsA) mem md, AR segsA B ly S W mem md ->
  arodata_okP segsA 0x9b6e0 0x9cb68 B (aview segsA (w_H W) mem) ->
  Forall (fun g => range_addressable (aview segsA (w_H W) mem) SHADOW_OFF (fst g) (snd g)) (hi_globs rate_himg_A) /\
  Forall (fun s => rt_cstr segsA (w_H W) mem (fst s) (snd s)) (hi_strs rate_himg_A) /\
  rt_ro_cells segsA (w_H W) mem (hi_cells rate_himg_A) /\
  Forall (fun t => rt_i32tab segsA (w_H W) mem (fst t) (snd t)) (hi_i32 rate_himg_A) /\
  Forall (fun t => rt_u64tab segsA (w_H W) mem (fst t) (snd t)) (hi_u64 rate_himg_A).
Proof.
intros B HF ly S W mem md HAR HA.
exact (rt_static_of_img_facts segsA B rate_himg_A IMG_LO IMG_TOP 0x9b6e0 0x9cb68 HF rate_A_img_static
  ly S W mem md HAR HA).
Qed.
(* With RtPgBase.rt_rom_pinned (the owned read-only bytes pinned as AR constant cells) also rom_view: every conjunct
   of the main walk's chaining law RtPgSeg.v rh_static_law at image A's segments and RO_LO / RO_HI. *)
Lemma rate_A_static_full : forall B : asyms, rt_img_facts segsA B rate_himg_A IMG_LO IMG_TOP ->
  rt_rom_pinned segsA B ->
  forall ly S (W : world segsA) mem md, AR segsA B ly S W mem md ->
  arodata_okP segsA 0x9b6e0 0x9cb68 B (aview segsA (w_H W) mem) ->
  Forall (fun g => range_addressable (aview segsA (w_H W) mem) SHADOW_OFF (fst g) (snd g)) (hi_globs rate_himg_A) /\
  Forall (fun s => rt_cstr segsA (w_H W) mem (fst s) (snd s)) (hi_strs rate_himg_A) /\
  rt_ro_cells segsA (w_H W) mem (hi_cells rate_himg_A) /\
  Forall (fun t => rt_i32tab segsA (w_H W) mem (fst t) (snd t)) (hi_i32 rate_himg_A) /\
  Forall (fun t => rt_u64tab segsA (w_H W) mem (fst t) (snd t)) (hi_u64 rate_himg_A) /\
  rom_view segsA W mem.
Proof.
intros B HF HP ly S W mem md HAR HA.
destruct (rate_A_static_of_facts B HF ly S W mem md HAR HA) as (A1 & A2 & A3 & A4 & A5).
split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|].
exact (rt_rom_view_of segsA B 0x9b6e0 0x9cb68 ly S W mem md HP HAR HA).
Qed.
End st.
Print Assumptions rate_A_static_of_facts.
Print Assumptions rate_A_static_full.
