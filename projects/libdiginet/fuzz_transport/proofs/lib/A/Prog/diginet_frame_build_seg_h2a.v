(* diginet_frame_build_seg_h2a: the piece FB_H2 -> FB_H2B of the image-A walk of diginet_frame_build
   (fuzz_frame.asan, entry 0x8267c; the run 0x82840 .. 0x828f4), as a footprint run stepped by lib/Lib/StepF.v.
   The run writes six bytes at out + 16 .. out + 21: the sum (a2 then a1, put16 sm), then the send counter read by
   the 4-byte `lwu` at s3 + 4 = hp + 4, stored big endian (put32 send). Each store and the load has its instrumented
   check before it: srli by 3, add the shadow base, `lb` of the shadow byte, `bnez`.
   Every shadow byte the run reads is 0, so no slow path runs: the last byte of each checked granule lies inside the
   addressable range (out + 12, 18 bytes for the stores at out + 16 .. out + 21; hp + 4, 12 bytes for the load), so
   fb_ck_of_addressable with an access width of 8 leaves only the 0 case (fb_shadow0). The addressability of each
   range is carried across the stores by fb_addressable_tp. The 30-or-more bytes at out are cut into a 16-byte block,
   the six bytes as C1 cells and the rest (fb_cut6), so that StepF's mem_after_store updates one cell per store; the
   cells are joined back at the end (fb_h2a_cells). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportSyms DgnTransportAddr AsanKA AsanKAProof.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_frame_build_iface.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(** * Shadow facts *)

(* Every shadow byte of the run is 0: an 8-byte window from x inside an addressable range holds the last byte of
   x's granule. *)
Lemma fb_shadow0 : forall m q n x, addressable m q n -> q <= x -> x + 8 <= q + n ->
  exists b : byte, mrd rsegs m (wa (shadow_addr x)) = Some b /\ bv_signed b = 0.
Proof.
  intros m q n x HA H1 H2.
  destruct (fb_ck_of_addressable m q n x 8 HA H1 H2 ltac:(lia)) as (b & Hb & C).
  exists b. split; [exact Hb|].
  pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia.
Qed.

Lemma fb_app_of : forall m q n lo hi, addressable m q n -> q <= lo -> hi <= q + n ->
  forall a, lo <= a < hi -> app_mem a.
Proof.
  intros m q n lo hi (_ & _ & _ & HA) H1 H2 a Ha.
  destruct (HA (a - q) ltac:(lia)) as (Happ & _).
  replace (q + (a - q)) with a in Happ by lia. exact Happ.
Qed.

(* The shadow byte of x, a <= x <= e, lies in the shadow range of [a, e]. *)
Lemma fb_sh_rng1 : forall RNG a e x, a <= x <= e ->
  ExecF.rng RNG (shadow_addr a) (shadow_addr e - shadow_addr a + 1) -> ExecF.rng RNG (shadow_addr x) 1.
Proof.
  intros RNG a e x Hx H. eapply rng_sub'; [exact H|]. unfold shadow_addr. Z.div_mod_to_equations. lia.
Qed.

(** * Reads *)

Lemma fb_rd_all : forall m A bs, bytes_at rsegs m A bs ->
  ov_read_bytes rsegs m (Z_to_bv 64 A) (length bs) = Some bs.
Proof.
  intros m A bs H.
  pose proof (bytes_at_read rsegs m A bs 0 (length bs) H ltac:(lia) ltac:(cbn; lia)) as R.
  rewrite Z.add_0_r in R. cbn [Z.to_nat skipn] in R. rewrite firstn_all in R. exact R.
Qed.

(* `lwu` of a 32-bit value. *)
Lemma fb_zx32 : forall z, 0 <= z < 2 ^ 32 -> zx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold zx32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

(** * The six cells at out + 16 *)

Lemma fb_map_C1 : forall mid : list byte,
  cells_wf (map C1 mid) /\ cells_bytes (map C1 mid) = mid /\ cells_size (map C1 mid) = length mid.
Proof.
  induction mid as [|b mid IH]; [cbn; split; [exact I | split; reflexivity]|].
  destruct IH as (A1 & A2 & A3). cbn [map cells_wf cell_wf cells_bytes cbytes cells_size csize length app].
  rewrite A2, A3. split; [split; [exact I | exact A1] | split; reflexivity].
Qed.

Lemma fb_rw_cut : forall m A pre mid post,
  rw_cells rsegs m A [CB (length (pre ++ mid ++ post)) (pre ++ mid ++ post)] ->
  rw_cells rsegs m A (CB (length pre) pre :: map C1 mid ++ [CB (length post) post]).
Proof.
  intros m A pre mid post [[_ Hb] Hw].
  destruct (fb_map_C1 mid) as (W1 & B1 & S1).
  split; [split|].
  - cbn [cells_wf cell_wf]. split; [reflexivity|]. apply cells_wf_app. split; [exact W1|].
    cbn. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes]. rewrite cells_bytes_app, B1. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb.
  - cbn [cells_size csize]. rewrite cells_size_app, S1. cbn [cells_size csize].
    cbn [cells_size csize] in Hw.
    assert (E : (length pre + (length mid + (length post + 0)) = length (pre ++ mid ++ post) + 0)%nat)
      by (rewrite !length_app; lia).
    rewrite E. exact Hw.
Qed.

Lemma fb_rw_glue : forall m A pre mid post,
  rw_cells rsegs m A (CB (length pre) pre :: map C1 mid ++ [CB (length post) post]) ->
  rw_cells rsegs m A [CB (length (pre ++ mid ++ post)) (pre ++ mid ++ post)].
Proof.
  intros m A pre mid post [[_ Hb] Hw].
  destruct (fb_map_C1 mid) as (W1 & B1 & S1).
  split; [split|].
  - cbn [cells_wf cell_wf]. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r.
    cbn [cells_bytes cbytes] in Hb. rewrite cells_bytes_app, B1 in Hb. cbn [cells_bytes cbytes] in Hb.
    rewrite app_nil_r in Hb. exact Hb.
  - cbn [cells_size csize]. cbn [cells_size csize] in Hw. rewrite cells_size_app, S1 in Hw.
    cbn [cells_size csize] in Hw.
    assert (E : (length (pre ++ mid ++ post) + 0 = length pre + (length mid + (length post + 0)))%nat)
      by (rewrite !length_app; lia).
    rewrite E. exact Hw.
Qed.

Lemma fb_len6 : forall mid : list byte, length mid = 6%nat ->
  exists x0 x1 x2 x3 x4 x5, mid = [x0; x1; x2; x3; x4; x5].
Proof.
  intros mid H.
  destruct mid as [|x0 mid]; [cbn in H; lia|].
  destruct mid as [|x1 mid]; [cbn in H; lia|].
  destruct mid as [|x2 mid]; [cbn in H; lia|].
  destruct mid as [|x3 mid]; [cbn in H; lia|].
  destruct mid as [|x4 mid]; [cbn in H; lia|].
  destruct mid as [|x5 mid]; [cbn in H; lia|].
  destruct mid as [|x6 mid]; [|cbn in H; lia].
  exists x0, x1, x2, x3, x4, x5. reflexivity.
Qed.

Lemma fb_cut6 : forall m A l, (22 <= length l)%nat -> rw_cells rsegs m A [CB (length l) l] ->
  exists pre x0 x1 x2 x3 x4 x5 post, l = pre ++ [x0; x1; x2; x3; x4; x5] ++ post /\ length pre = 16%nat /\
    rw_cells rsegs m A [CB 16 pre; C1 x0; C1 x1; C1 x2; C1 x3; C1 x4; C1 x5; CB (length post) post].
Proof.
  intros m A l Hl H.
  pose proof (CB3_bytes 16 6 l ltac:(lia)) as E.
  assert (L6 : length (firstn 6 (skipn 16 l)) = 6%nat) by (rewrite length_firstn, length_skipn; lia).
  assert (L16 : length (firstn 16 l) = 16%nat) by (rewrite length_firstn; lia).
  destruct (fb_len6 _ L6) as (x0 & x1 & x2 & x3 & x4 & x5 & E6).
  rewrite E6 in E.
  exists (firstn 16 l), x0, x1, x2, x3, x4, x5, (skipn (16 + 6) l).
  split; [symmetry; exact E|]. split; [exact L16|].
  rewrite <- E in H. apply fb_rw_cut in H. rewrite L16 in H. exact H.
Qed.

(* The six stored bytes, joined back into the block at out. *)
Lemma fb_h2a_cells : forall m A l pre post x0 x1 x2 x3 x4 x5 y0 y1 y2 y3 y4 y5,
  l = pre ++ [x0; x1; x2; x3; x4; x5] ++ post -> length pre = 16%nat ->
  rw_cells rsegs m A [CB 16 pre; C1 y0; C1 y1; C1 y2; C1 y3; C1 y4; C1 y5; CB (length post) post] ->
  rw_cells rsegs m A [CB (length l) (fb_put l 16 [y0; y1; y2; y3; y4; y5])].
Proof.
  intros m A l pre post x0 x1 x2 x3 x4 x5 y0 y1 y2 y3 y4 y5 El Lp H.
  assert (EP : fb_put l 16 [y0; y1; y2; y3; y4; y5] = pre ++ [y0; y1; y2; y3; y4; y5] ++ post).
  { subst l. unfold fb_put. rewrite <- Lp. rewrite firstn_app_exact. f_equal. f_equal.
    replace (length pre + length [y0; y1; y2; y3; y4; y5])%nat
      with (length (pre ++ [x0; x1; x2; x3; x4; x5])) by (rewrite length_app; reflexivity).
    rewrite app_assoc. apply skipn_app_exact. }
  assert (EL : length l = length (pre ++ [y0; y1; y2; y3; y4; y5] ++ post))
    by (subst l; rewrite !length_app; reflexivity).
  rewrite EP, EL. apply fb_rw_glue. rewrite Lp. exact H.
Qed.

(** * The run *)

Ltac fb_mem k := lazymatch goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) => k mm end.

(* The byte Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z)) is Z_to_bv 8 z. *)
Lemma fb_c1_lit : forall z, Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z)) = Z_to_bv 8 z.
Proof.
  intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 8) with (2 ^ 8).
  rewrite (Z.mod_eq z (2 ^ 64)) by lia.
  replace (z - 2 ^ 64 * (z / 2 ^ 64)) with (z + - (2 ^ 56 * (z / 2 ^ 64)) * 2 ^ 8) by lia.
  apply Z_mod_plus_full.
Qed.

(* A store step. transport's StepF updates the cell in the step and stores the byte `le1 (Z_to_bv 64 z)` as
   C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z))); the cell lists are rewritten to the byte Z_to_bv 8 z. *)
Ltac fb_st :=
  step;
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => rewrite ?le1_lit_byte; mem_after_store
  | _ => idtac
  end;
  repeat match goal with
  | H : rw_cells _ _ _ ?cs |- _ =>
      match cs with context [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 ?z))] => rewrite (fb_c1_lit z) in H end
  end.

Lemma fb_h2a_F : fb_h2a_stmt.
Proof.
  unfold fb_h2a_stmt.
  intros RNG ra sp gp tp t0 t1 t2 s1 a0 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m
    out hp send ack retry cmd ncmds sm l HO HOL HL HH HHL HSD HAK HRT HCM HNC HSM HDJ RW BH AO AH
    ROUT RHP RSO RSH.
  let v := eval vm_compute in FB_H2 in change FB_H2 with v.
  let v := eval vm_compute in FB_H2B in change FB_H2B with v.
  unfold ASAN_K.
  clear HAK HRT HCM HNC.
  unfold fb_hdr_in in BH. apply bytes_at_app in BH. destruct BH as [BA4 _].
  pose proof (fb_app_of m (out + 12) 18 (out + 16) (out + 22) AO ltac:(lia) ltac:(lia)) as HAPP.
  pose proof (fb_sh_rng1 RNG (out + 12) (out + 29) (out + 16) ltac:(lia) RSO) as RS16.
  pose proof (fb_sh_rng1 RNG (out + 12) (out + 29) (out + 17) ltac:(lia) RSO) as RS17.
  pose proof (fb_sh_rng1 RNG (out + 12) (out + 29) (out + 18) ltac:(lia) RSO) as RS18.
  pose proof (fb_sh_rng1 RNG (out + 12) (out + 29) (out + 19) ltac:(lia) RSO) as RS19.
  pose proof (fb_sh_rng1 RNG (out + 12) (out + 29) (out + 20) ltac:(lia) RSO) as RS20.
  pose proof (fb_sh_rng1 RNG (out + 12) (out + 29) (out + 21) ltac:(lia) RSO) as RS21.
  pose proof (fb_sh_rng1 RNG (hp + 4) (hp + 15) (hp + 4) ltac:(lia) RSH) as RSP.
  clear RSO RSH.
  destruct (fb_cut6 m out l ltac:(lia) RW) as (pre & x0 & x1 & x2 & x3 & x4 & x5 & post & El & Lpre & RWc).
  clear RW.
  pose proof (munch_refl [(out + 16, out + 22)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (U16 : bv_unsigned (Z_to_bv 64 (out + 16)) = out + 16) by (apply unsigned_lit; lia).
  assert (U17 : bv_unsigned (Z_to_bv 64 (out + 17)) = out + 17) by (apply unsigned_lit; lia).
  assert (U18 : bv_unsigned (Z_to_bv 64 (out + 18)) = out + 18) by (apply unsigned_lit; lia).
  assert (U19 : bv_unsigned (Z_to_bv 64 (out + 19)) = out + 19) by (apply unsigned_lit; lia).
  assert (U20 : bv_unsigned (Z_to_bv 64 (out + 20)) = out + 20) by (apply unsigned_lit; lia).
  assert (U21 : bv_unsigned (Z_to_bv 64 (out + 21)) = out + 21) by (apply unsigned_lit; lia).
  assert (UP : bv_unsigned (Z_to_bv 64 (hp + 4)) = hp + 4) by (apply unsigned_lit; lia).
  (* ---- out + 16: 0x82840 addi a0,s0,16; 0x82844 srli a3,a0,3; 0x82848 add a3,a3,s10; 0x8284c lb a3,0(a3);
     0x82850 bnez a3 ---- *)
  step.
  step. gen_shr (Z_to_bv 64 (out + 16)) g16 G16. rewrite U16 in G16.
  step. gen_addi g16 h16 H16.
  assert (E16 : bv_unsigned h16 = shadow_addr (out + 16))
    by (rewrite H16, G16; unfold shadow_addr, ASAN_K; lia).
  clear H16 G16.
  fb_mem ltac:(fun mm => destruct (fb_shadow0 mm (out + 12) 18 (out + 16)
    (fb_addressable_tp m mm (out + 12) 18 (out + 16) (out + 22) MU HAPP AO) ltac:(lia) ltac:(lia))
    as (b16 & M16 & C16)).
  rewrite <- E16 in RS16.
  pose proof (rdw0 _ h16 _ _ M16 E16) as R. step. clear R.
  step. rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C16); cbn [negb].
  clear M16 C16 E16 RS16.
  (* 0x82854 sb a2,16(s0) *)
  fb_st.
  (* ---- out + 17: 0x82858 addi a0,s0,17; 0x8285c srli a2,a0,3; 0x82860 add a2,a2,s10; 0x82864 lb a2,0(a2);
     0x82868 bnez a2 ---- *)
  step.
  step. gen_shr (Z_to_bv 64 (out + 17)) g17 G17. rewrite U17 in G17.
  step. gen_addi g17 h17 H17.
  assert (E17 : bv_unsigned h17 = shadow_addr (out + 17))
    by (rewrite H17, G17; unfold shadow_addr, ASAN_K; lia).
  clear H17 G17.
  fb_mem ltac:(fun mm => destruct (fb_shadow0 mm (out + 12) 18 (out + 17)
    (fb_addressable_tp m mm (out + 12) 18 (out + 16) (out + 22) MU HAPP AO) ltac:(lia) ltac:(lia))
    as (b17 & M17 & C17)).
  rewrite <- E17 in RS17.
  pose proof (rdw0 _ h17 _ _ M17 E17) as R. step. clear R.
  step. rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C17); cbn [negb].
  clear M17 C17 E17 RS17.
  (* 0x8286c sb a1,17(s0) *)
  fb_st.
  (* ---- hp + 4 (the 4-byte load): 0x82870 addi a0,s3,4; 0x82874 srli a1,a0,3; 0x82878 add a1,a1,s10;
     0x8287c lb a1,0(a1); 0x82880 bnez a1 ---- *)
  step.
  step. gen_shr (Z_to_bv 64 (hp + 4)) gP GP. rewrite UP in GP.
  step. gen_addi gP hP HP.
  assert (EP : bv_unsigned hP = shadow_addr (hp + 4))
    by (rewrite HP, GP; unfold shadow_addr, ASAN_K; lia).
  clear HP GP.
  fb_mem ltac:(fun mm => destruct (fb_shadow0 mm (hp + 4) 12 (hp + 4)
    (fb_addressable_tp m mm (hp + 4) 12 (out + 16) (out + 22) MU HAPP AH) ltac:(lia) ltac:(lia))
    as (bP & MP & CP)).
  rewrite <- EP in RSP.
  pose proof (rdw0 _ hP _ _ MP EP) as R. step. clear R.
  step. rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) CP); cbn [negb].
  clear MP CP EP RSP.
  (* ---- out + 18: 0x82884 addi a1,s0,18; 0x82888 srli a2,a1,3; 0x8288c add a2,a2,s10; 0x82890 lb a3,0(a2);
     0x82894 lwu a2,0(a0); 0x82898 bnez a3 ---- *)
  step.
  step. gen_shr (Z_to_bv 64 (out + 18)) g18 G18. rewrite U18 in G18.
  step. gen_addi g18 h18 H18.
  assert (E18 : bv_unsigned h18 = shadow_addr (out + 18))
    by (rewrite H18, G18; unfold shadow_addr, ASAN_K; lia).
  clear H18 G18.
  fb_mem ltac:(fun mm => destruct (fb_shadow0 mm (out + 12) 18 (out + 18)
    (fb_addressable_tp m mm (out + 12) 18 (out + 16) (out + 22) MU HAPP AO) ltac:(lia) ltac:(lia))
    as (b18 & M18 & C18)).
  rewrite <- E18 in RS18.
  pose proof (rdw0 _ h18 _ _ M18 E18) as R. step. clear R.
  fb_mem ltac:(fun mm => pose proof (fb_rd_all mm (hp + 4) _ BA4) as R4). rewrite length_le4 in R4.
  step. clear R4.
  rewrite (fb_zx32 send HSD).
  step. rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C18); cbn [negb].
  clear M18 C18 E18 RS18.
  (* 0x8289c srli a1,a2,24; 0x828a0 addi a0,s0,19; 0x828a4 sb a1,18(s0) *)
  step. step. fb_st.
  (* ---- out + 19: 0x828a8 srli a1,a0,3; 0x828ac add a1,a1,s10; 0x828b0 lb a1,0(a1); 0x828b4 bnez a1 ---- *)
  step. gen_shr (Z_to_bv 64 (out + 19)) g19 G19. rewrite U19 in G19.
  step. gen_addi g19 h19 H19.
  assert (E19 : bv_unsigned h19 = shadow_addr (out + 19))
    by (rewrite H19, G19; unfold shadow_addr, ASAN_K; lia).
  clear H19 G19.
  fb_mem ltac:(fun mm => destruct (fb_shadow0 mm (out + 12) 18 (out + 19)
    (fb_addressable_tp m mm (out + 12) 18 (out + 16) (out + 22) MU HAPP AO) ltac:(lia) ltac:(lia))
    as (b19 & M19 & C19)).
  rewrite <- E19 in RS19.
  pose proof (rdw0 _ h19 _ _ M19 E19) as R. step. clear R.
  step. rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C19); cbn [negb].
  clear M19 C19 E19 RS19.
  (* 0x828b8 srli a1,a2,16; 0x828bc addi a0,s0,20; 0x828c0 sb a1,19(s0) *)
  step. step. fb_st.
  (* ---- out + 20: 0x828c4 srli a1,a0,3; 0x828c8 add a1,a1,s10; 0x828cc lb a1,0(a1); 0x828d0 bnez a1 ---- *)
  step. gen_shr (Z_to_bv 64 (out + 20)) g20 G20. rewrite U20 in G20.
  step. gen_addi g20 h20 H20.
  assert (E20 : bv_unsigned h20 = shadow_addr (out + 20))
    by (rewrite H20, G20; unfold shadow_addr, ASAN_K; lia).
  clear H20 G20.
  fb_mem ltac:(fun mm => destruct (fb_shadow0 mm (out + 12) 18 (out + 20)
    (fb_addressable_tp m mm (out + 12) 18 (out + 16) (out + 22) MU HAPP AO) ltac:(lia) ltac:(lia))
    as (b20 & M20 & C20)).
  rewrite <- E20 in RS20.
  pose proof (rdw0 _ h20 _ _ M20 E20) as R. step. clear R.
  step. rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C20); cbn [negb].
  clear M20 C20 E20 RS20.
  (* 0x828d4 srli a1,a2,8; 0x828d8 addi a0,s0,21; 0x828dc sb a1,20(s0) *)
  step. step. fb_st.
  (* ---- out + 21: 0x828e0 srli a1,a0,3; 0x828e4 add a1,a1,s10; 0x828e8 lb a1,0(a1); 0x828ec bnez a1 ---- *)
  step. gen_shr (Z_to_bv 64 (out + 21)) g21 G21. rewrite U21 in G21.
  step. gen_addi g21 h21 H21.
  assert (E21 : bv_unsigned h21 = shadow_addr (out + 21))
    by (rewrite H21, G21; unfold shadow_addr, ASAN_K; lia).
  clear H21 G21.
  fb_mem ltac:(fun mm => destruct (fb_shadow0 mm (out + 12) 18 (out + 21)
    (fb_addressable_tp m mm (out + 12) 18 (out + 16) (out + 22) MU HAPP AO) ltac:(lia) ltac:(lia))
    as (b21 & M21 & C21)).
  rewrite <- E21 in RS21.
  pose proof (rdw0 _ h21 _ _ M21 E21) as R. step. clear R.
  step. rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C21); cbn [negb].
  clear M21 C21 E21 RS21.
  (* 0x828f0 sb a2,21(s0) *)
  fb_st.
  (* FB_H2B *)
  apply evtF_done.
  do 5 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
  lazymatch type of RWc with
  | rw_cells _ _ _ [_; C1 ?y0; C1 ?y1; C1 ?y2; C1 ?y3; C1 ?y4; C1 ?y5; _] =>
      replace (put16 sm ++ put32 send) with [y0; y1; y2; y3; y4; y5];
      [ eapply fb_h2a_cells; [exact El | exact Lpre | exact RWc] | ]
  end.
  unfold put16, put32, b8. cbn [app].
  rewrite !(unsigned_lit send) by lia. rewrite !Z.shiftr_div_pow2 by lia. reflexivity.
Qed.
