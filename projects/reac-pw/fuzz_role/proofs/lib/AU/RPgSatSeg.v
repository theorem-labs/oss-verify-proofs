(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgSatSeg.v at 0b7b3db186d; the same witness at
   I = lib/AU/RPgImgA.v's role_himg_B on lib/AU/Img0.v's rsegs: image B's 49 descriptors at 0x9f380, its two
   application spans, its class-4 frame (1024 bytes), its real frame of 0x200 bytes, the checked real-frame range
   R+0x178 .. R+0x187, its 41 strings, its 38 read-only cells and its read-only range 0x9a3c0 .. 0x9b7c8. *)
(* Image B's witness for the image-level premises of reac-pw/fuzz_role's segment contracts (lib/A/RPgCSpec.v
   role_build_contract and role_check_contract: rl_seg_pre, the C1 cut list hi_L1 and the C3 cut list hi_L3) at
   I = role_himg_B (lib/AU/RPgImgA.v). At one concrete state over image B's loaded segments, the frame's shadow
   bytes, the 49 registered globals, the checked real-frame range, the 41 strings, the read-only cells, the
   read-only data, the read-only segments and the live values at C1 and C3 hold together, so those premises are not
   vacuous on image B. Each shadow byte the witness memory holds is the one the runtime writes, and each program
   byte is read from the image.
   Pinned image: fuzz_role.asan-ubsan, sha256 b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0.
   proves no function (kind: statement text) *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YP09 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YO0f YG00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgImgA RPgSat.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ======================================== the registered globals ======================================== *)
(* All 49 descriptors of asan_globals [AG_START, AG_STOP) (lib/AU/RPgSat.v), in table order: (descriptor address,
   (beg, size, size_with_redzone)). The runtime registers them all (RPgSat.role_B_reg_chk). *)
Definition role_B_globals49 : list (Z * (Z * Z * Z)) :=
  [(0x9f380, (0x20f00, 14, 32)); (0x9f3c0, (0x20f20, 14, 32)); (0x9f400, (0x20f40, 14, 32));
   (0x9f440, (0x20f60, 15, 32)); (0x9f480, (0x20f80, 14, 32)); (0x9f4c0, (0x20fa0, 19, 64));
   (0x9f500, (0x20fe0, 13, 32)); (0x9f540, (0x21000, 16, 32)); (0x9f580, (0x21020, 13, 32));
   (0x9f5c0, (0x21040, 56, 96)); (0x9f600, (0x210a0, 84, 128)); (0x9f640, (0x21120, 16, 32));
   (0x9f680, (0x21140, 16, 32)); (0x9f6c0, (0x21160, 14, 32)); (0x9f700, (0x21180, 3, 32));
   (0x9f740, (0x211a0, 3, 32)); (0x9f780, (0x211c0, 3, 32)); (0x9f7c0, (0x211e0, 3, 32));
   (0x9f800, (0x21200, 21, 64)); (0x9f840, (0x21240, 1, 32)); (0x9f880, (0x21260, 2, 32));
   (0x9f8c0, (0x21280, 3, 32)); (0x9f900, (0x212a0, 3, 32)); (0x9f940, (0x212c0, 3, 32));
   (0x9f980, (0x212e0, 3, 32)); (0x9f9c0, (0x21300, 3, 32)); (0x9fa00, (0x21320, 4, 32));
   (0x9fa40, (0x21340, 22, 64)); (0x9fa80, (0x21380, 8, 32)); (0x9fac0, (0x213a0, 4, 32));
   (0x9fb00, (0x213c0, 5, 32)); (0x9fb40, (0x213e0, 4, 32)); (0x9fb80, (0x21400, 6, 32));
   (0x9fbc0, (0x21420, 10, 32)); (0x9fc00, (0x21440, 6, 32)); (0x9fc40, (0x21460, 2, 32));
   (0x9fc80, (0x21480, 25, 64)); (0x9fcc0, (0x214c0, 8, 32)); (0x9fd00, (0x214e0, 5, 32));
   (0x9fd40, (0x21500, 10, 32)); (0x9fd80, (0x21540, 5, 32)); (0x9fdc0, (0x21560, 10, 32));
   (0x9fe00, (0x21580, 25, 64)); (0x9fe40, (0x215c0, 8, 32)); (0x9fe80, (0x215e0, 14, 32));
   (0x9fec0, (0x9a7a0, 72, 128)); (0x9ff00, (0x9a820, 112, 160)); (0x9ff40, (0x9a8c0, 64, 96));
   (0x9ff80, (0x9a920, 16, 32))].

(* The application spans whose shadow bytes the witness memory holds. Each global's [beg, beg + size_with_redzone)
   lies in one of them, and the first holds every string's 64-byte blocks (the shadow hulls rl_cstr reads). *)
Definition seg_spans : list (Z * Z) := [(0x20f00, 0x21600); (0x9a7a0, 0x9a940)].

Definition gdummy : Z * (Z * Z * Z) := (0, (0, 0, 0)).
(* The 49 rows, measured with RPgSat.v's checkers: each descriptor's beg, size and size_with_redzone are the
   image's (globals_chk), the k-th row is the descriptor at AG_START + 64 k and the table holds 49; their ranges
   [beg, beg + size_with_redzone) are ascending and apart (so each granule has at most one global's shadow byte)
   and lie in seg_spans; each string of hi_strs is in the image with its NUL and is the global with beg = its
   address and size = its length + 1 (cstrs_img_chk). *)
Lemma role_B_globals49_chk :
  globals_chk segsB role_B_globals49 &&
  forallb (fun k => fst (nth k role_B_globals49 gdummy) =? AG_START + 64 * Z.of_nat k) (seq 0 49) &&
  (Z.of_nat (length role_B_globals49) =? (AG_STOP - AG_START) / 64) &&
  forallb (fun k => let '(_, (b1, _, r1)) := nth k role_B_globals49 gdummy in
                    let '(_, (b2, _, _)) := nth (S k) role_B_globals49 gdummy in b1 + r1 <=? b2) (seq 0 48) &&
  forallb (fun g => let '(_, (b, _, r)) := g in existsb (fun s => (fst s <=? b) && (b + r <=? snd s)) seg_spans)
    role_B_globals49 &&
  cstrs_img_chk segsB role_B_globals49 (hi_strs role_himg_B) = true.
Proof. vm_compute. reflexivity. Qed.
(* They are the rows of hi_globs (address, size). *)
Lemma role_B_globals49_globs :
  map (fun g => let '(_, (b, n, _)) := g in (b, n)) role_B_globals49 = hi_globs role_himg_B.
Proof. vm_compute. reflexivity. Qed.

(* ======================================== the run's quantities ======================================== *)
(* S the entry sp (a user stack address); R = (S - 0x200) & -32; F a class-4 side-stack frame (1024 bytes,
   1024-aligned); the pp block (16-aligned), the pod block and the input elsewhere in user memory. len, left and fl
   are values no conjunct below constrains beyond 0 <= fl < 256. *)
Definition env_seg : rl_env := {|
  e_S := 0x7fffffff0000; e_R := 0x7ffffffefe00; e_F := 0x7ff000000000;
  e_pp := 0x7e0000000010; e_pod := 0x7e0000010010; e_len := 16; e_fl := 0;
  e_src := 0x7d0000000001; e_left := 16 |}.

Definition rng_apartb (r1 r2 : Z * Z) : bool := (fst r1 + snd r1 <=? fst r2) || (fst r2 + snd r2 <=? fst r1).
Fixpoint all_apartb (l : list (Z * Z)) : bool :=
  match l with [] => true | r :: t => forallb (rng_apartb r) t && all_apartb t end.
(* The real frame [R, S), F's frame, the pp block, the pod block and the input (start, length). *)
Definition env_ranges (e : rl_env) : list (Z * Z) :=
  [(e_R e, e_S e - e_R e); (e_F e, YG00.fs_frame_bytes (hi_cid role_himg_B)); (e_pp e, Layout.PP_SIZE);
   (e_pod e, e_len e); (e_src e, e_left e)].
(* The choice: R = (S - 0x200) & -32 (the prologue's s1, RPgImgA.v's header), F 1024-aligned (the class-4 frame
   size), pp and pod 16-aligned; the five ranges lie above the image (kImgEnd) and below kHighMemEnd, pairwise
   apart. *)
Lemma env_seg_chk :
  (e_R env_seg =? Z.land (e_S env_seg - hi_rsz role_himg_B) (-32)) &&
  (e_F env_seg mod YG00.fs_frame_bytes (hi_cid role_himg_B) =? 0) &&
  (e_pp env_seg mod 16 =? 0) && (e_pod env_seg mod 16 =? 0) &&
  forallb (fun r => (kImgEnd <=? fst r) && (fst r + snd r <=? kHighMemEnd)) (env_ranges env_seg) &&
  all_apartb (env_ranges env_seg) = true.
Proof. vm_compute. reflexivity. Qed.

(* ================================================ the witness ================================================ *)
(* The real-frame cells (address, 8-byte value) that a cut list L names, at e. *)
Definition cut_cells (e : rl_env) (L : list (rl_loc * rl_x)) : list (Z * Z) :=
  flat_map (fun f => match fst f with
                     | LCell b o => [(rl_xv e b + o, rl_xv e (snd f) mod 2 ^ 64)]
                     | LReg _ => []
                     end) L.
Definition cells_seg : list (Z * Z) := cut_cells env_seg (hi_L1 role_himg_B ++ hi_L3 role_himg_B).

(* The byte at u >= SHADOW_OFF: the shadow byte of a granule in seg_spans (RPgSat.granule_shadow over the 49
   globals: 0 for a full granule, size mod 8 for the last partial one, 0xf9 for a redzone one, and the 0 of the
   freshly mapped shadow for the one gap [0x21520, 0x21540) no global covers); the frame's shadow bytes hi_shA from
   shadow_addr F; 0 for the shadow bytes of the real-frame ranges hi_rz; the bytes of the cells of hi_L1 and hi_L3;
   else none. *)
Definition byte_seg (u : Z) : option Z :=
  if existsb (fun r => (shadow_addr (fst r) <=? u) && (u <? shadow_addr (snd r))) seg_spans
  then Some (granule_shadow role_B_globals49 ((u - SHADOW_OFF) * 8))
  else if (shadow_addr (e_F env_seg) <=? u) &&
          (u <? shadow_addr (e_F env_seg) + Z.of_nat (length (hi_shA role_himg_B)))
  then Some (nth (Z.to_nat (u - shadow_addr (e_F env_seg))) (hi_shA role_himg_B) 0)
  else if existsb (fun z => (shadow_addr (e_R env_seg + fst z) <=? u) &&
                            (u <=? shadow_addr (e_R env_seg + fst z + snd z - 1))) (hi_rz role_himg_B)
  then Some 0
  else match find (fun c => (fst c <=? u) && (u <? fst c + 8)) cells_seg with
       | Some c => Some (YO0f.le_byte (snd c) 8 (Z.to_nat (u - fst c)))
       | None => None
       end.
(* The witness memory: nothing below SHADOW_OFF (so no byte of the image, and every program byte is read through
   mbyte's fall-back to seg_rom), byte_seg above. No byte is hidden (RPgSat.H_w). *)
Definition mem_seg : word -> option byte := fun w =>
  if bv_unsigned w <? SHADOW_OFF then None else option_map (fun v => Z_to_bv 8 v) (byte_seg (bv_unsigned w)).

(* The register map at a cut: each register L names holds the value L gives at e, and sp holds R. *)
Definition cut_regs (e : rl_env) (L : list (rl_loc * rl_x)) : bvmap 5 word :=
  fold_right (fun f m => match fst f with
                         | LReg r => regupd m (Z_to_bv 5 r) (Z_to_bv 64 (rl_xv e (snd f)))
                         | LCell _ _ => m
                         end)
    (regupd bvmap_empty (Z_to_bv 5 2) (Z_to_bv 64 (e_R e))) L.
Definition regs1_seg : bvmap 5 word := cut_regs env_seg (hi_L1 role_himg_B).
Definition regs3_seg : bvmap 5 word := cut_regs env_seg (hi_L3 role_himg_B).

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

(* rl_cstr for each string of a list. *)
Definition strs_chk (h : word -> bool) (mem : word -> option byte) (l : list (Z * list Z)) : bool :=
  forallb (fun c => cstr_chk segsB h mem (fst c) (snd c)) l.
Lemma strs_chk_ok : forall h mem l, strs_chk h mem l = true -> Forall (fun s => rl_cstr segsB h mem (fst s) (snd s)) l.
Proof.
intros h mem l H. apply Forall_forall. intros c Hc. cbv beta. apply cstr_chk_ok.
unfold strs_chk in H. rewrite forallb_forall in H. exact (H c Hc).
Qed.

(* RPgBase.rl_at and rl_cut. *)
Definition at_chk (h : word -> bool) (mem : word -> option byte) (regs : bvmap 5 word) (e : rl_env)
  (l : rl_loc) (v : Z) : bool :=
  match l with
  | LReg r => bv_unsigned (getr regs (Z_to_bv 5 r)) =? bv_unsigned (Z_to_bv 64 v)
  | LCell b o => val_chk segsB (mrestrict h mem) (rl_xv e b + o) 8 (v mod 2 ^ 64)
  end.
Lemma at_chk_ok : forall h mem regs e l v, at_chk h mem regs e l v = true -> rl_at segsB h mem regs e l v.
Proof.
intros h mem regs e [r|b o] v E; unfold at_chk in E; unfold rl_at.
- apply bv_eq. apply Z.eqb_eq. exact E.
- apply val_chk_ok. exact E.
Qed.
Definition cut_chk (h : word -> bool) (mem : word -> option byte) (regs : bvmap 5 word) (e : rl_env)
  (L : list (rl_loc * rl_x)) : bool :=
  forallb (fun f => at_chk h mem regs e (fst f) (rl_xv e (snd f))) L.
Lemma cut_chk_ok : forall h mem regs e L, cut_chk h mem regs e L = true -> rl_cut segsB h mem regs e L.
Proof.
intros h mem regs e L H. unfold rl_cut. apply Forall_forall. intros f Hf. cbv beta. apply at_chk_ok.
unfold cut_chk in H. rewrite forallb_forall in H. exact (H f Hf).
Qed.

(* Every loaded segment ends at or below kImgEnd (< SHADOW_OFF). *)
Definition segsB_end_chk : bool := forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? kImgEnd) segsB.
Lemma segsB_end_chk_ok : segsB_end_chk = true.
Proof. vm_compute. reflexivity. Qed.
Lemma segsB_end : forall s, In s segsB -> Z.of_N (seg_base s) + Z.of_N (seg_size s) <= kImgEnd.
Proof.
intros s Hs. pose proof segsB_end_chk_ok as E. unfold segsB_end_chk in E. rewrite forallb_forall in E.
apply Z.leb_le. exact (E s Hs).
Qed.

(* Below SHADOW_OFF the witness reads the image. *)
Lemma mem_seg_low : forall a, 0 <= a < SHADOW_OFF -> mem_seg (Z_to_bv 64 a) = None.
Proof.
intros a Ha. unfold mem_seg.
assert (Hu : bv_unsigned (Z_to_bv 64 a) = a).
{ rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). unfold SHADOW_OFF in Ha. lia. }
assert (Hlt : (a <? SHADOW_OFF) = true) by (apply Z.ltb_lt; lia).
rewrite Hu, Hlt. reflexivity.
Qed.
Lemma aview_low : forall a, 0 <= a < SHADOW_OFF ->
  aview segsB H_w mem_seg a = option_map (fun b : byte => bv_unsigned b) (seg_rom segsB (Z_to_bv 64 a)).
Proof. intros a Ha. unfold aview, mbyte, mrestrict, H_w. rewrite (mem_seg_low a Ha). reflexivity. Qed.

(* ============================== the conjuncts at the witness, one by one ============================== *)
(* 1. The frame's shadow bytes after the prologue. *)
Lemma fsh_B_chk : bytes_chk (aview segsB H_w mem_seg) (shadow_addr (e_F env_seg)) (hi_shA role_himg_B) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma fsh_B : rl_fsh segsB H_w mem_seg (e_F env_seg) (hi_shA role_himg_B).
Proof. unfold rl_fsh. exact (bytes_chk_ok _ _ _ fsh_B_chk). Qed.

(* 2. The 49 registered globals. *)
Lemma globs_B_chk : ranges_chk (aview segsB H_w mem_seg) (fun a => a) (hi_globs role_himg_B) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma globs_B :
  Forall (fun g => range_addressable (aview segsB H_w mem_seg) SHADOW_OFF (fst g) (snd g)) (hi_globs role_himg_B).
Proof. exact (ranges_chk_ok _ _ _ globs_B_chk). Qed.

(* 3. The real-frame ranges the code shadow-checks. *)
Lemma rz_B_chk : ranges_chk (aview segsB H_w mem_seg) (fun o => e_R env_seg + o) (hi_rz role_himg_B) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rz_B :
  Forall (fun z => range_addressable (aview segsB H_w mem_seg) SHADOW_OFF (e_R env_seg + fst z) (snd z))
    (hi_rz role_himg_B).
Proof. exact (ranges_chk_ok _ _ _ rz_B_chk). Qed.

(* 4. The 41 strings. *)
Lemma strs_B_chk : strs_chk H_w mem_seg (hi_strs role_himg_B) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma strs_B : Forall (fun s => rl_cstr segsB H_w mem_seg (fst s) (snd s)) (hi_strs role_himg_B).
Proof. exact (strs_chk_ok _ _ _ strs_B_chk). Qed.

(* 5. The read-only cells. *)
Lemma cells_B_chk : cells_chk segsB (mrestrict H_w mem_seg) (hi_cells role_himg_B) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cells_B : rl_ro_cells segsB H_w mem_seg (hi_cells role_himg_B).
Proof. unfold rl_ro_cells. exact (cells_chk_ok _ _ _ cells_B_chk). Qed.

(* 6. The read-only data, for every symbol record B: RO_LO = 0x9a3c0 and RO_HI = 0x9b7c8 (image B's .data.rel.ro
   start and .got end, lib/AU/RPgLib.v) and every read-only segment lie below SHADOW_OFF. *)
Lemma aro_B : forall B : asyms, arodata_okP segsB 0x9a3c0 0x9b7c8 B (aview segsB H_w mem_seg).
Proof.
intros B a Hro _ _. apply aview_low. hnf in Hro. destruct Hro as [(s & Hs & _ & Hr) | Hr].
- pose proof (segsB_end s Hs) as Hb. pose proof (N2Z.is_nonneg (seg_base s)) as H0.
  unfold kImgEnd in Hb. unfold SHADOW_OFF. lia.
- unfold SHADOW_OFF. lia.
Qed.

(* 7. The live values at C1 (regs1_seg) and at C3 (regs3_seg, a0 = pod), over the same memory. *)
Lemma cut1_B_chk : cut_chk H_w mem_seg regs1_seg env_seg (hi_L1 role_himg_B) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cut1_B : rl_cut segsB H_w mem_seg regs1_seg env_seg (hi_L1 role_himg_B).
Proof. exact (cut_chk_ok _ _ _ _ _ cut1_B_chk). Qed.
Lemma cut3_B_chk : cut_chk H_w mem_seg regs3_seg env_seg (hi_L3 role_himg_B) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cut3_B : rl_cut segsB H_w mem_seg regs3_seg env_seg (hi_L3 role_himg_B).
Proof. exact (cut_chk_ok _ _ _ _ _ cut3_B_chk). Qed.

(* 8. The run's quantities. *)
Lemma env_B : 0 <= e_fl env_seg < 256 /\ e_pp env_seg <> 0 /\ e_R env_seg mod 16 = 0 /\
  e_R env_seg + hi_rsz role_himg_B <= e_S env_seg.
Proof.
split; [split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity|].
split; [apply Z.eqb_neq; vm_compute; reflexivity|].
split; [apply Z.eqb_eq; vm_compute; reflexivity|].
apply Z.leb_le. vm_compute. reflexivity.
Qed.

(* 9. Every byte of a read-only segment reads as the image's, at every world whose hidden set is H_w. *)
Lemma rom_B : forall W : world segsB, w_H W = H_w -> rom_view segsB W mem_seg.
Proof.
intros W HW a Ha. rewrite HW. apply aview_low. hnf in Ha. destruct Ha as (s & Hs & _ & Hr).
pose proof (segsB_end s Hs) as Hb. pose proof (N2Z.is_nonneg (seg_base s)) as H0.
unfold kImgEnd in Hb. unfold SHADOW_OFF. lia.
Qed.

(* ================================================ the lemma ================================================ *)
(* The image-level conjuncts of rl_seg_pre at I = role_himg_B (RLO = 0x9a3c0, RHI = 0x9b7c8), the C1 list hi_L1 and
   the C3 list hi_L3 hold together at one state (H, mem, regs, regs3, e). *)
Lemma rl_seg_static_B : exists (H : word -> bool) (mem : word -> option byte) (regs regs3 : bvmap 5 word) (e : rl_env),
  rl_fsh segsB H mem (e_F e) (hi_shA role_himg_B) /\
  Forall (fun g => range_addressable (aview segsB H mem) SHADOW_OFF (fst g) (snd g)) (hi_globs role_himg_B) /\
  Forall (fun z => range_addressable (aview segsB H mem) SHADOW_OFF (e_R e + fst z) (snd z)) (hi_rz role_himg_B) /\
  Forall (fun s => rl_cstr segsB H mem (fst s) (snd s)) (hi_strs role_himg_B) /\
  rl_ro_cells segsB H mem (hi_cells role_himg_B) /\
  (forall B : asyms, arodata_okP segsB 0x9a3c0 0x9b7c8 B (aview segsB H mem)) /\
  rl_cut segsB H mem regs e (hi_L1 role_himg_B) /\
  rl_cut segsB H mem regs3 e (hi_L3 role_himg_B) /\
  0 <= e_fl e < 256 /\ e_pp e <> 0 /\ e_R e mod 16 = 0 /\ e_R e + hi_rsz role_himg_B <= e_S e /\
  (forall W : world segsB, w_H W = H -> rom_view segsB W mem).
Proof.
exists H_w, mem_seg, regs1_seg, regs3_seg, env_seg.
split; [exact fsh_B|].
split; [exact globs_B|].
split; [exact rz_B|].
split; [exact strs_B|].
split; [exact cells_B|].
split; [exact aro_B|].
split; [exact cut1_B|].
split; [exact cut3_B|].
destruct env_B as (E1 & E2 & E3 & E4).
split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|].
exact rom_B.
Qed.
Print Assumptions rl_seg_static_B.

(* At C4 the role granule 0x54 is 0x04 (hi_shB): the same memory with that one shadow byte set satisfies rl_fsh
   with hi_shB. *)
Definition mem_segB : word -> option byte := fun w =>
  if bv_unsigned w =? shadow_addr (e_F env_seg) + 0x54 then Some (Z_to_bv 8 0x04) else mem_seg w.
Lemma fshB_B_chk : bytes_chk (aview segsB H_w mem_segB) (shadow_addr (e_F env_seg)) (hi_shB role_himg_B) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rl_seg_shB_B : rl_fsh segsB H_w mem_segB (e_F env_seg) (hi_shB role_himg_B) /\
  (forall w, bv_unsigned w <> shadow_addr (e_F env_seg) + 0x54 -> mem_segB w = mem_seg w).
Proof.
split; [unfold rl_fsh; exact (bytes_chk_ok _ _ _ fshB_B_chk)|].
intros w Hw. unfold mem_segB. apply Z.eqb_neq in Hw. rewrite Hw. reflexivity.
Qed.
Print Assumptions rl_seg_shB_B.
