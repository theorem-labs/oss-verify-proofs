(* crtB_encbcmp: the piece CRT_LOOP_OUT -> CRT_RET_BCMP of the cgif-form walk of check_round_trip on image B
   (fuzz_decode.asan-ubsan): `crtB_encbcmp_stmt` of lib/B/Prog/crtB_cuts.v, the cut contract at CRT_LOOP_OUT from
   the one at CRT_RET_BCMP, in the backward-chain form of cgif's ACey.v:270-330.

   The run, read backwards from the cut after bcmp:
     CRT_LOOP_OUT .. CRT_AT 0x284   crtB_segs.v crt_seg5_F (ld s0,8(sp); a0 = R; a1 = a3 = nch from 40(sp);
                                    a2 = Q; a4 = ns; jal reac_braid_encode), carried into SRr by crtB_walk.v crtB_run;
     the call                       the braid leaf's cg contract (crtB_rules' dec_leaf_wr_at at the loop's float
                                    state), its post re-establishing the inner journal (YCbq.v:517
                                    ajournal_after_write: it wrote its stack window and the temporary R);
     CRT_AT 0x288 .. CRT_AT 0x294   crt_seg6_F (a0 = R; a1 = audio from 24(sp); a2 = 3 nch ns from 16(sp);
                                    jal bcmp);
     the call                       abcmp_realizes through YCbq.v:2062 aj_bcmp_at;
     CRT_RET_BCMP                   crtB_at_bcmp, with a0 = 0: bcmp answers 0 because R now holds the braid of the
                                    loop's float rows (CrtEnc.v rb_rows_at / rb_cover), which is the caller's audio
                                    (dec_crt_braid at the entry reader, the inner journal keeps the audio block).
   No instrumented access lies between CRT_LOOP_OUT and CRT_RET_BCMP (the ld's are stack slots): the only guard
   on this stretch is the `bnez a0` at CRT_RET_BCMP into the abort block, refuted by the next piece from a0 = 0.

   The braid leaf is the Theorem Labs lane statement (lib/B/Prog/reac_braid_encode_cg.v, a working branch
   77469213fc2): no mem_inv and no shadow_rw; its read-only premises (:70-73) over
   REAC_BRAID_ENCODE_RO_RD come from the cut's crtB_rom_on (crtB_ls_ro), the vm_computed fact that this set lies
   in a non-writable loaded segment (crtB_braid_ro_rom) and the stack window being above the image
   (crtB_ls_frame_off).  The piece is proved for any RO_RD holding REAC_BRAID_ENCODE_RO_RD (crtB_encbcmp_sub) and
   closed at the statement's DEC_RO_RD, where that inclusion is vm_computed (crtB_encbcmp). *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n YK1b.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG01 YG0f YG0n YG0d YCbq YC5d YGCalloc YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YP09 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Frame Cells Step Regs6ss ExecF.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import DecodeBSyms DecodeBAddr DecodeBList.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require LeafCgKit reac_braid_encode_cg crt_braid_need check_braid_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import crtB_iface check_round_trip_cg crtB_cuts.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import crtB_walk crtB_cells crtB_segs crtB_glue.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog Require FloatExact RcBraid RcBraidLib.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require CrtEnc.
Import ListNotations.
Open Scope Z_scope.
Module BC := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.AsanCells.
Module CE := OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib.CrtEnc.
Module RBr := OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog.RcBraid.
Module RBL := OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog.RcBraidLib.
Module BN := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.crt_braid_need.

(* ---- image facts ---- *)

(* The braid encoder's entry is the listing's: crt_braid_need.v names it by value. *)
Lemma crtB_enc_pc : CRT_ENCODE = BN.REAC_BRAID_ENCODE.
Proof. vm_compute. reflexivity. Qed.

Lemma crtB_pcs : (0 <= CRT_RET_ENCODE < 2 ^ 64) /\ (0 <= CRT_RET_BCMP < 2 ^ 64) /\
  (bv_unsigned (Z_to_bv 64 CRT_RET_ENCODE) mod 2 = 0) /\ (bv_unsigned (Z_to_bv 64 CRT_RET_BCMP) mod 2 = 0).
Proof.
  split; [split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity|].
  split; [split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity|].
  split; vm_compute; reflexivity.
Qed.

(* image B's loaded segments are one contiguous run over [IMG_LO, IMG_TOP) (page-rounded). *)
Fixpoint crtB_chain (l : list Segment) (lo hi : Z) : bool :=
  match l with
  | [] => Z.eqb lo hi
  | s :: t => andb (Z.eqb (Z.of_N (seg_base s)) lo) (crtB_chain t (Z.of_N (seg_base s) + Z.of_N (seg_size s)) hi)
  end.

Lemma crtB_chain_cover : forall l lo hi, crtB_chain l lo hi = true -> forall a, lo <= a < hi ->
  exists s, In s l /\ Z.of_N (seg_base s) <= a /\ a + 1 <= Z.of_N (seg_base s) + Z.of_N (seg_size s).
Proof.
  induction l as [|s t IH]; intros lo hi H a Ha; cbn [crtB_chain] in H.
  - apply Z.eqb_eq in H. lia.
  - apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1.
    destruct (Z_lt_le_dec a (Z.of_N (seg_base s) + Z.of_N (seg_size s))) as [Hl|Hg].
    + exists s. split; [left; reflexivity | lia].
    + destruct (IH _ _ H2 a ltac:(lia)) as (s' & Hin & Hs). exists s'. split; [right; exact Hin | exact Hs].
Qed.

Lemma crtB_chain_B : crtB_chain decodesegsB0 YImgTop.IMG_LO YImgTop.IMG_TOP = true.
Proof. vm_compute. reflexivity. Qed.

Lemma crtB_img_bounds : 0 <= YImgTop.IMG_LO /\ YImgTop.IMG_LO < YImgTop.IMG_TOP /\ YImgTop.IMG_TOP <= kLowMemEnd.
Proof. rewrite YImgTop.IMG_LO_val, YImgTop.IMG_TOP_val. unfold kLowMemEnd. lia. Qed.

Lemma crtB_in_img_of : forall a, YImgTop.IMG_LO <= a < YImgTop.IMG_TOP -> in_img decodesegsB0 a.
Proof.
  intros a Ha. destruct (crtB_chain_cover _ _ _ crtB_chain_B a Ha) as (s & Hin & H1 & H2).
  exists s. split; [exact Hin | lia].
Qed.

Lemma crtB_img_vis : forall (W : world decodesegsB0) a, YImgTop.IMG_LO <= a < YImgTop.IMG_TOP ->
  w_H W (wa a) = false.
Proof.
  intros W a Ha. destruct (w_H W (wa a)) eqn:E; [exfalso | reflexivity].
  pose proof (w_Hoff W _ E) as Hf.
  pose proof crtB_img_bounds as (B0 & B1 & B2). unfold kLowMemEnd in B2.
  unfold wa in Hf. rewrite (unsigned_lit a) in Hf by lia.
  destruct (crtB_chain_cover _ _ _ crtB_chain_B a Ha) as (s & Hin & H1 & H2).
  exact (crt_find_none _ _ _ s Hf Hin H1 H2).
Qed.

(* A byte off the image that aview sees is a visible byte. *)
Lemma crtB_vis_av : forall (W : world decodesegsB0) mem s, 0 <= s < 2 ^ 64 -> ~ in_img decodesegsB0 s ->
  aview decodesegsB0 (w_H W) mem s <> None -> w_H W (wa s) = false.
Proof.
  intros W mem s Hs Hn Hv. destruct (w_H W (wa s)) eqn:E; [exfalso | reflexivity].
  apply Hv. unfold aview, YP09.mbyte, mrestrict. cbv beta. unfold wa in E. rewrite E.
  rewrite (seg_rom_none decodesegsB0 s Hs Hn). reflexivity.
Qed.

(* ---- shadow arithmetic ---- *)
Lemma crtB_sh_bc : forall x, BC.shadow_addr x = shadow_addr x.
Proof. intros x. unfold BC.shadow_addr, shadow_addr, BC.ASAN_K, SHADOW_OFF. lia. Qed.

Lemma crtB_sh_of : forall x, shadow_of_addr SHADOW_OFF x = shadow_addr x.
Proof. intros x. unfold shadow_of_addr, shadow_addr. reflexivity. Qed.

Lemma crtB_signed8 : forall b : byte, bv_unsigned b < 128 -> bv_signed b = bv_unsigned b.
Proof.
  intros b Hb. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
  unfold bv_signed, bv_swrap, bv_wrap. change (bv_half_modulus 8) with 128. change (bv_modulus 8) with 256.
  rewrite Z.mod_small by lia. lia.
Qed.

(* ---- the braid byte map over the entry reader ---- *)
Lemma crtB_s24_mod : forall b0 b1 b2, 0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 ->
  crtB_s24 b0 b1 b2 mod 2 ^ 24 = b0 + 256 * b1 + 65536 * b2.
Proof.
  intros b0 b1 b2 H0 H1 H2. unfold crtB_s24. destruct (128 <=? b2).
  - replace (b0 + 256 * b1 + 65536 * b2 - 16777216) with ((b0 + 256 * b1 + 65536 * b2) + (-1) * 2 ^ 24) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.sub_0_r. apply Z.mod_small. lia.
Qed.

Lemma crtB_s24_rng : forall b0 b1 b2, 0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 ->
  - 2 ^ 23 <= crtB_s24 b0 b1 b2 < 2 ^ 23.
Proof.
  intros b0 b1 b2 H0 H1 H2. unfold crtB_s24.
  destruct (Z.leb_spec 128 b2); lia.
Qed.

Lemma crtB_s24_byte : forall b0 b1 b2 j, 0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= j < 3 ->
  CE.rb_byte (crtB_s24 b0 b1 b2 mod 2 ^ 24) j mod 256 = (if j =? 0 then b0 else if j =? 1 then b1 else b2).
Proof.
  intros b0 b1 b2 j H0 H1 H2 Hj. rewrite crtB_s24_mod by assumption. unfold CE.rb_byte.
  assert (C : j = 0 \/ j = 1 \/ j = 2) by lia.
  destruct C as [-> | [-> | ->]]; cbn [Z.eqb Pos.eqb].
  - replace (b0 + 256 * b1 + 65536 * b2) with (b0 + (b1 + 256 * b2) * 256) by ring.
    rewrite Z.mod_add by lia. rewrite (Z.mod_small b0 256) by lia. apply Z.mod_small. lia.
  - replace (b0 + 256 * b1 + 65536 * b2) with (b0 + (b1 + 256 * b2) * 256) by ring.
    rewrite Z.div_add by lia. rewrite (Z.div_small b0 256) by lia. rewrite Z.add_0_l.
    replace (b1 + 256 * b2) with (b1 + b2 * 256) by ring. rewrite Z.mod_add by lia.
    rewrite (Z.mod_small b1 256) by lia. apply Z.mod_small. lia.
  - replace (b0 + 256 * b1 + 65536 * b2) with ((b0 + 256 * b1) + b2 * 65536) by ring.
    rewrite Z.div_add by lia. rewrite (Z.div_small (b0 + 256 * b1) 65536) by lia. rewrite Z.add_0_l.
    apply Z.mod_small. lia.
Qed.

Lemma crtB_braid_off_at : forall N s c j, 0 <= c -> 0 <= j < 3 ->
  3 * (s * N + 2 * (c / 2)) + DCBc.braid_off c j = CE.rb_at N s c j.
Proof.
  intros N s c j Hc Hj. rewrite CE.rb_at_eq by lia. unfold DCBc.braid_off, CE.rb_off. rewrite (Zmod_even c).
  destruct (Z.even c); destruct (j =? 0); destruct (j =? 1); lia.
Qed.

Lemma crtB_pb_rng : forall (H : word -> bool) mem pcm i, 0 <= crtB_pb (aview decodesegsB0 H mem) pcm i < 256.
Proof.
  intros H mem pcm i. unfold crtB_pb.
  destruct (aview decodesegsB0 H mem (pcm + i)) as [v|] eqn:E; [|lia].
  destruct (aview_byte _ _ _ _ _ E) as (b & _ & _ & R). exact R.
Qed.

Lemma crtB_not_in_wr : forall lo hi x, ~ (lo <= x < hi) -> ~ LeafCgKit.in_wr [(lo, hi)] x.
Proof.
  intros lo hi x Hn H. unfold LeafCgKit.in_wr in H. apply Exists_cons in H as [H|H].
  - exact (Hn H).
  - apply Exists_nil in H. exact H.
Qed.

Lemma crtB_in_wr1 : forall lo hi x, LeafCgKit.in_wr [(lo, hi)] x -> lo <= x < hi.
Proof.
  intros lo hi x H. unfold LeafCgKit.in_wr in H. apply Exists_cons in H as [H|H].
  - exact H.
  - apply Exists_nil in H. destruct H.
Qed.

(* callee-saved registers survive both the leaf's and the bcmp's post *)
Lemma crtB_regs_pres : forall regs ra rb Q ns, crtB_regs regs ra Q ns ->
  (forall r, acallee_saved r -> YK11.getr rb (Z_to_bv 5 r) = YK11.getr ra (Z_to_bv 5 r)) ->
  crtB_regs regs rb Q ns.
Proof.
  intros regs ra rb Q ns (R2 & R3 & R4 & R18 & R21 & R24) E.
  assert (A : forall r, acallee_saved r -> YK11.getr rb (Z_to_bv 5 r) = YK11.getr ra (Z_to_bv 5 r)) by exact E.
  split; [change (YK11.getr rb (Z_to_bv 5 2) = w64 (spZ regs - CRT_FRAME)); rewrite A by (unfold acallee_saved; lia); exact R2|].
  split; [change (YK11.getr rb (Z_to_bv 5 3) = YK11.getr regs 3); rewrite A by (unfold acallee_saved; lia); exact R3|].
  split; [change (YK11.getr rb (Z_to_bv 5 4) = YK11.getr regs 4); rewrite A by (unfold acallee_saved; lia); exact R4|].
  split; [change (YK11.getr rb (Z_to_bv 5 18) = w64 ns); rewrite A by (unfold acallee_saved; lia); exact R18|].
  split; [change (YK11.getr rb (Z_to_bv 5 21) = w64 Q); rewrite A by (unfold acallee_saved; lia); exact R21|].
  change (YK11.getr rb (Z_to_bv 5 24) = w64 BC.ASAN_K); rewrite A by (unfold acallee_saved; lia); exact R24.
Qed.

Section EncBcmp.
Context {rc : YM05.RunCeil}.
Local Notation segs := decodesegsB0.
Variable B : asyms.
Variable MT : ameter_ops.
Variable RO_RD : list (Z * Z).
Local Notation GR r i := (YKK.getr r (Z_to_bv 5 i)).

(* The braid leaf's read-only read set lies in the cuts' read-only set (REAC_BRAID_ENCODE_RO_RD is a sub-list of
   the statement's DEC_RO_RD, crtB_braid_ro_sub_dec); discharged in crtB_encbcmp at RO_RD := DEC_RO_RD. *)
Hypothesis HRO_SUB : forall a, (exists r, In r LBraidB.REAC_BRAID_ENCODE_RO_RD /\ fst r <= a < fst r + snd r) ->
  crtB_in_ro_rd RO_RD a.

Section Blk.
Hypothesis LAWS : AR_laws segs B.

Lemma crtB_blk : forall ly S (W : world segs) mem md p n,
  AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  p mod 16 = 0 /\ 4096 <= p /\ 0 <= n /\ n <= req_size n /\ p + req_size n <= YM05.alloc_ceiling /\
  in_app p (req_size n) /\
  (forall a, p <= a < p + req_size n -> apresent (w_H W) mem a /\ ~ aowned B ly S a /\ ~ in_img segs a).
Proof.
  intros ly S W mem md p n HAR Hin.
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (H16 & H4096 & Hc & Happ & Hb & _ & Hn).
  pose proof (req_size_pos n ltac:(lia)) as [Rq1 Rq2].
  split; [exact H16|]. split; [exact H4096|]. split; [lia|]. split; [exact Rq2|]. split; [exact Hc|].
  split; [exact Happ|].
  intros a Ha. destruct (Hb a Ha) as [Hp Ho]. split; [exact Hp|]. split; [exact Ho|].
  exact (blk_img _ _ LAWS ly S W mem md p n a HAR Hin Ha).
Qed.

Lemma crtB_sep : forall ly S (W : world segs) mem md x l y,
  AR segs B ly S W mem md -> Permutation (ablocks B ly S) (x :: l) -> In y l ->
  fst x + req_size (snd x) <= fst y \/ fst y + req_size (snd y) <= fst x.
Proof.
  intros ly S W mem md x l y HAR HP Hy.
  destruct (in_split y l Hy) as (l1 & l2 & ->).
  assert (HP2 : Permutation (ablocks B ly S) (x :: y :: l1 ++ l2)).
  { eapply perm_trans; [exact HP|]. apply perm_skip. apply Permutation_sym. apply Permutation_middle. }
  exact (sep_blocks_perm _ _ LAWS ly S W mem md x y _ HAR HP2).
Qed.

(* decode's `addressable` of a slice of a live block, from AR's block shadow *)
Lemma crtB_addr : forall ly S (W : world segs) mem md p n a len,
  AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) -> p <= a -> a + len <= p + req_size n -> 0 <= len ->
  BC.addressable mem a len.
Proof.
  intros ly S W mem md p n a len HAR Hin H1 H2 Hl.
  destruct (crtB_blk ly S W mem md p n HAR Hin) as (H16 & H4096 & Hn0 & Hnq & Hc & Happ & Hb).
  pose proof (range_addressable_of_block segs B LAWS ly S W mem md p n a len HAR Hin H1 H2) as RA.
  pose proof asan_consts as (AC & _ & HMB & HME & HLE).
  split; [lia|]. split; [exact Hl|]. split; [unfold BC.APPMEM_END; lia|].
  intros i Hi. split.
  - destruct Happ as [Hp4096 [HL | [HH1 HH2]]];
      unfold BC.app_mem, BC.LOWMEM_END, BC.HIGHMEM_BEG, BC.APPMEM_END;
      unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia.
  - destruct (RA (a + i) ltac:(lia)) as (sv & Hsv & Hok).
    destruct (aview_byte segs _ _ _ _ Hsv) as (b & Hmb & Ev & Hr). subst sv.
    exists b. split.
    + rewrite crtB_sh_bc, <- crtB_sh_of.
      set (sx := shadow_of_addr SHADOW_OFF (a + i)) in *.
      assert (Hsx : SHADOW_OFF <= sx < 2 ^ 64)
        by (unfold sx, shadow_of_addr, SHADOW_OFF; Z.div_mod_to_equations; lia).
      assert (Hni : ~ in_img segs sx)
        by (intros Hi'; apply crtB_segs_low in Hi'; unfold kLowMemEnd, SHADOW_OFF in *; lia).
      unfold YP09.mbyte, mrestrict in Hmb. cbv beta in Hmb.
      destruct (w_H W (Z_to_bv 64 sx)) eqn:Eh; try rewrite Eh in Hmb; cbv iota in Hmb.
      * rewrite (seg_rom_none segs sx ltac:(unfold SHADOW_OFF in Hsx; lia) Hni) in Hmb. discriminate Hmb.
      * unfold mrd, wa. exact Hmb.
    + unfold saddr_ok in Hok. rewrite crtB_signed8 by lia. unfold BC.shadow_ok. lia.
Qed.
End Blk.

(* a shadow hull AR sees is inside the walk's footprint *)
Lemma crtB_rng_hull : forall (Wx : world segs) mem d n, 4096 <= d -> d + n <= 2 ^ 47 -> 0 < n ->
  shadow_hull_vis (aview segs (w_H Wx) mem) d n ->
  ExecF.rng (LCK.RNG_W (world segs) (@w_H segs) Wx) (BC.shadow_addr d / 8 * 8)
    (BC.shadow_addr (d + n - 1) / 8 * 8 + 8 - BC.shadow_addr d / 8 * 8).
Proof.
  intros Wx mem d n H0 H1 Hn HV. rewrite !crtB_sh_bc.
  assert (L1 : SHADOW_OFF <= shadow_addr d / 8 * 8)
    by (unfold shadow_addr, SHADOW_OFF; Z.div_mod_to_equations; lia).
  assert (L2 : shadow_addr (d + n - 1) / 8 * 8 + 8 <= 2 ^ 47)
    by (unfold shadow_addr, SHADOW_OFF; Z.div_mod_to_equations; lia).
  apply crtB_rng_of_vis; [unfold SHADOW_OFF in L1; lia | lia |].
  intros a Ha. apply (crtB_vis_av Wx mem a); [unfold SHADOW_OFF in L1; lia | |].
  - intros Hi. apply crtB_segs_low in Hi. unfold kLowMemEnd, SHADOW_OFF in *. lia.
  - apply HV. lia.
Qed.

(* ---- the braid leaf's read-only premises (reac_braid_encode_cg.v:70-73): its read-only read set
   REAC_BRAID_ENCODE_RO_RD lies in a non-writable loaded segment (decided by vm_compute), so decode's mrd is the
   ROM there (from the cut's crtB_rom_on) and the stack window is off it (the image is below kLowMemEnd). ---- *)
Lemma crtB_braid_ro_rom_b :
  forallb (fun r => existsb (fun s => (Z.of_N (seg_base s) <=? fst r) && (fst r + snd r <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))
                                      && negb (seg_writable s))%bool decodesegsB0)
    LBraidB.REAC_BRAID_ENCODE_RO_RD = true.
Proof. vm_compute. reflexivity. Qed.

Lemma crtB_braid_ro_rom : forall a, (exists r, In r LBraidB.REAC_BRAID_ENCODE_RO_RD /\ fst r <= a < fst r + snd r) ->
  in_rom segs a.
Proof.
  intros a (r & Hr & Ha). pose proof crtB_braid_ro_rom_b as C. rewrite forallb_forall in C.
  specialize (C r Hr). apply existsb_exists in C as (s & Hs & Hb). cbv beta in Hb.
  apply andb_prop in Hb as [Hb Hw]. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  apply negb_true_iff in Hw. exists s. split; [exact Hs|]. split; [exact Hw | lia].
Qed.

Lemma crtB_ls_ro : forall (Wx : world segs) mem, crtB_rom_on RO_RD Wx mem ->
  forall x : word, crtB_in_ro_rd RO_RD (bv_unsigned x) -> in_rom segs (bv_unsigned x) -> mrd rsegs mem x = seg_rom rsegs x.
Proof.
  intros Wx mem HR x Hin Hrom.
  pose proof (HR (bv_unsigned x) Hin Hrom) as Hv.
  assert (Hh : w_H Wx (wa (bv_unsigned x)) = false).
  { destruct (w_H Wx (wa (bv_unsigned x))) eqn:E; [exfalso | reflexivity].
    unfold wa in E. rewrite Z_to_bv_bv_unsigned in E. pose proof (w_Hoff Wx x E) as Hn.
    destruct Hrom as (sg & Hsg & _ & H1 & H2).
    exact (crt_find_none segs (bv_unsigned x) 1 sg Hn Hsg H1 ltac:(lia)). }
  rewrite (crtB_aview_mrd (w_H Wx) mem (bv_unsigned x) Hh) in Hv.
  unfold wa in Hv. rewrite Z_to_bv_bv_unsigned in Hv.
  exact (crtB_opt_byte_eq _ _ Hv).
Qed.

(* rom_view on RO_RD survives a step that keeps aview on the image *)
Lemma crtB_rom_keep : forall (Wx : world segs) memX memY, crtB_rom_on RO_RD Wx memX ->
  (forall a, in_img segs a -> aview segs (w_H Wx) memY a = aview segs (w_H Wx) memX a) ->
  crtB_rom_on RO_RD Wx memY.
Proof.
  intros Wx memX memY HR HK a Hin Hrom.
  assert (Him : in_img segs a) by (destruct Hrom as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]).
  rewrite (HK a Him). exact (HR a Hin Hrom).
Qed.

Section Fixed.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z)
  (regs : bvmap 5 word) (audio pcm nch ns bA nA bP nP T : Z) (ch : list (Z * Z * Z))
  (ly1 : alayout) (S1 : astate) (W1 : world segs) (P Q R : Z) (v0 v32 : word).
Hypothesis LAWS : AR_laws segs B.
Hypothesis HCELLS : dec_crt_cells B.
Hypothesis RBC : forall fx' : YKK.FPState,
  @abcmp_realizes fx' rc segs B (decodeb_sigma DB___interceptor_trampoline_bcmp).
Hypothesis REL : forall fx' : YKK.FPState, @dec_leaf_wr_at rc B (@LBraidB.dec_reac_braid_encode_cg) fx'.
Hypothesis HB : crtB_at_bcmp B MT RO_RD.
Hypothesis HPRE :
  crtB_pre B MT RO_RD STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs audio pcm nch ns bA nA bP nP T ch.
Hypothesis HFRS : frames S1 = frames Sc.
Hypothesis HMO : mo_le MT Sc S1 (crtB_acc3 MT nch ns).
Hypothesis HBL : crtB_blocks3 B lyc Sc ly1 S1 P Q R nch ns.

Local Notation POST := (@dec_crt_post rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs nch ns).
Local Notation INNER memX mdX :=
  (@ajournal rc dec_B_sink_head segs B DEC_CRT_STK (spZ regs) [] lyc Sc W memc mdc [] ly1 S1 W1 memX mdX 3).
Local Notation FRAMEOK memX :=
  (crtB_frame regs memX audio v0 (w64 R) (w64 (3 * (nch * ns))) v32 (w64 nch) (w64 P)).
Local Notation NN := (3 * (nch * ns)).

Lemma crtB_F_num : 2 <= nch <= 127 /\ 1 <= ns <= 12 /\ 3 * nch * ns <= 1440 /\ nch mod 2 = 0.
Proof.
  pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HEV & HN & HNS & HKB & _).
  split; [exact HN|]. split; [exact HNS|]. split; [exact HKB|].
  pose proof (Zmod_even nch) as E. rewrite HEV in E. exact E.
Qed.

Lemma crtB_F_inR : In (R, NN) (ablocks B ly1 S1).
Proof. destruct HBL as (HPERM & _). eapply Permutation_in; [apply Permutation_sym; exact HPERM|]. left. reflexivity. Qed.
Lemma crtB_F_inQ : In (Q, 8 * nch) (ablocks B ly1 S1).
Proof.
  destruct HBL as (HPERM & _). eapply Permutation_in; [apply Permutation_sym; exact HPERM|]. right. left. reflexivity.
Qed.
Lemma crtB_F_inP : In (P, 4 * (nch * ns)) (ablocks B ly1 S1).
Proof.
  destruct HBL as (HPERM & _). eapply Permutation_in; [apply Permutation_sym; exact HPERM|].
  right. right. left. reflexivity.
Qed.
Lemma crtB_F_inA : In (bA, nA) (ablocks B ly1 S1).
Proof.
  pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HINA & _).
  destruct HBL as (HPERM & _). eapply Permutation_in; [apply Permutation_sym; exact HPERM|].
  right. right. right. exact HINA.
Qed.

Lemma crtB_F_sep : forall memX mdX, AR segs B ly1 S1 W1 memX mdX ->
  (R + req_size NN <= Q \/ Q + req_size (8 * nch) <= R) /\
  (R + req_size NN <= P \/ P + req_size (4 * (nch * ns)) <= R) /\
  (R + req_size NN <= bA \/ bA + req_size nA <= R) /\
  ~ In (R, NN) (ablocks B lyc Sc).
Proof.
  intros memX mdX HAR. pose proof crtB_F_num as (HN & HNS & _).
  pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HINA & _).
  destruct HBL as (HPERM & _).
  split; [exact (crtB_sep LAWS _ _ _ _ _ _ _ _ HAR HPERM (or_introl eq_refl))|].
  split; [exact (crtB_sep LAWS _ _ _ _ _ _ _ _ HAR HPERM (or_intror (or_introl eq_refl)))|].
  split; [exact (crtB_sep LAWS _ _ _ _ _ _ _ _ HAR HPERM (or_intror (or_intror HINA)))|].
  intros Hin. pose proof (crtB_sep LAWS _ _ _ _ _ _ _ _ HAR HPERM (or_intror (or_intror Hin))) as D.
  cbn [fst snd] in D. pose proof (req_size_pos NN ltac:(nia)) as [Rq _]. lia.
Qed.

Lemma crtB_F_stk : forall memX mdX, INNER memX mdX ->
  AR segs B ly1 S1 W1 memX mdX /\
  (forall a, spZ regs - DEC_CRT_STK <= a < spZ regs -> apresent (w_H W1) memX a) /\
  YM05.alloc_ceiling + DEC_CRT_STK <= spZ regs /\ spZ regs <= 2 ^ 47.
Proof.
  intros memX mdX HJ.
  destruct HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRES & HSTK & _ & _).
  destruct HSTK as (_ & _ & Hceil & Hlo & Hhi & H47 & _).
  split; [exact HAR|]. split; [exact HPRES|]. split; lia.
Qed.

Lemma crtB_F_esp : forall regsX memX mdX, INNER memX mdX -> crtB_regs regs regsX Q ns ->
  bv_unsigned (GR regsX 2) = spZ regs - CRT_FRAME.
Proof.
  intros regsX memX mdX HJ HR. destruct HR as (E2 & _).
  destruct (crtB_F_stk memX mdX HJ) as (_ & _ & Hc & H47).
  pose proof asan_consts as (AC & _).
  replace (GR regsX 2) with (w64 (spZ regs - CRT_FRAME)) by (symmetry; exact E2).
  apply unsigned_lit. unfold CRT_FRAME, DEC_CRT_STK, DEC_CRT_FRAME, ASTACK in *. lia.
Qed.

Lemma crtB_aj_md : forall memX mdX mdY, INNER memX mdX -> same_but_materialized mdX mdY -> INNER memX mdY.
Proof.
  intros memX mdX mdY HJ HS.
  eapply ajournal_exec with (Wr := fun _ => False);
    solve [ exact LAWS | exact crtB_segs_low | exact HJ | exact HS | intros x _; reflexivity
          | intros x Hx; exact Hx | intros a F; destruct F ].
Qed.

Lemma crtB_F_frame_keep : forall memX mdX memY,
  INNER memX mdX -> FRAMEOK memX ->
  (forall a, apresent (w_H W1) memX a -> apresent (w_H W1) memY a) ->
  (forall a, spZ regs - CRT_FRAME <= a < spZ regs -> aview segs (w_H W1) memY a = aview segs (w_H W1) memX a) ->
  FRAMEOK memY.
Proof.
  intros memX mdX memY HJ HF HG HK.
  destruct (crtB_F_stk memX mdX HJ) as (_ & HPRES & Hc & H47).
  unfold crtB_frame in *.
  apply (crtB_rw_cells_kept W1 W1 memX memY _ _ HF).
  intros a Ha. unfold crt_fr in Ha. cbn [cells_size csize Nat.add] in Ha.
  assert (Hw : spZ regs - CRT_FRAME <= a < spZ regs) by (unfold CRT_FRAME in *; lia).
  assert (Hp : apresent (w_H W1) memX a)
    by (apply HPRES; unfold CRT_FRAME, DEC_CRT_STK, DEC_CRT_FRAME, ASTACK in *; lia).
  split; [exact Hp|]. split; [exact (HG a Hp)|]. exact (HK a Hw).
Qed.

(* the braid leaf's read-only bytes are off the stack window (both frames) *)
Lemma crtB_ls_frame_off : forall memX mdX, INNER memX mdX ->
  forall x, (exists r, In r LBraidB.REAC_BRAID_ENCODE_RO_RD /\ fst r <= x < fst r + snd r) ->
  ~ (spZ regs - DEC_CRT_STK <= x < spZ regs).
Proof.
  intros memX mdX HJ x Hx Ha.
  destruct (crtB_F_stk memX mdX HJ) as (_ & _ & Hc & _). pose proof asan_consts as (AC & _).
  pose proof (crtB_braid_ro_rom x Hx) as Hrom.
  assert (Him : in_img segs x) by (destruct Hrom as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]).
  pose proof (crtB_segs_low x Him) as Hl. unfold kLowMemEnd, DEC_CRT_STK, DEC_CRT_FRAME, ASTACK in *. lia.
Qed.

(* ---- at bcmp's entry (CRT_AT 0x294's target): the bcmp call, then the cut at CRT_RET_BCMP ---- *)
Lemma crtB_st_bcmp : forall (fxc : YKK.FPState) (regs4 : bvmap 5 word) mem md,
  INNER mem md -> crtB_rom_on RO_RD W1 mem -> FRAMEOK mem -> crtB_regs regs regs4 Q ns ->
  YKK.getr regs4 1 = Z_to_bv 64 CRT_RET_BCMP -> YKK.getr regs4 8 = w64 R ->
  YKK.getr regs4 10 = w64 R -> YKK.getr regs4 11 = w64 audio -> YKK.getr regs4 12 = w64 NN ->
  frm_zero (@fp_csr fxc) ->
  (forall i, 0 <= i < NN -> aview segs (w_H W1) mem (R + i) = aview segs (w_H W1) mem (audio + i)) ->
  SRr segs W1 (mkCfg (@YKK.mkst fxc regs4 (Z_to_bv 64 CRT_BCMP) mem (YKK.seg_rom segs)) md) POST.
Proof.
  intros fxc regs4 mem md HJ HROM HF HREGS Hra Hs0 Ha0 Ha1 Ha2 HFRM HEQ.
  pose proof crtB_F_num as (HN & HNS & HKB & HEV).
  pose proof HPRE as (_ & _ & _ & HGP & HTP & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HINA & HBA1 & HBA2 & _).
  destruct (crtB_F_stk mem md HJ) as (HAR & HPRES & Hc & H47).
  pose proof asan_consts as (AC & _).
  pose proof (crtB_F_esp regs4 mem md HJ HREGS) as ESP.
  pose proof HREGS as (E2 & E3 & E4 & E18 & E21 & E24).
  destruct (crtB_blk LAWS _ _ _ _ _ _ _ HAR crtB_F_inR) as (R16 & R4096 & Rn0 & Rnq & Rc & Rapp & RB).
  destruct (crtB_blk LAWS _ _ _ _ _ _ _ HAR crtB_F_inA) as (A16 & A4096 & An0 & Anq & Ac & Aapp & AB).
  assert (HNN : 0 < NN <= 1440) by nia.
  assert (HBA2' : audio + NN <= bA + nA) by nia.
  assert (Hsp : spZ regs4 = spZ regs + -160).
  { unfold spZ at 1. change (YKK.getr regs4 2) with (GR regs4 2). rewrite ESP. unfold CRT_FRAME. lia. }
  assert (Hsx : src_ok segs W1 regs4 mem R NN).
  { intros a Ha. split.
    - apply aview_some_of_apresent. exact (proj1 (RB a ltac:(lia))).
    - rewrite Hsp. unfold ESTACK, DEC_CRT_STK, DEC_CRT_FRAME, ASTACK in *. lia. }
  assert (Hsy : src_ok segs W1 regs4 mem audio NN).
  { intros a Ha. split.
    - apply aview_some_of_apresent. exact (proj1 (AB a ltac:(lia))).
    - rewrite Hsp. unfold ESTACK, DEC_CRT_STK, DEC_CRT_FRAME, ASTACK in *. lia. }
  assert (Hbx : forall a, R <= a < R + NN -> ~ (spZ regs + -160 - 2 * ESTACK <= a < spZ regs + -160))
    by (intros a Ha; unfold ESTACK, DEC_CRT_STK, DEC_CRT_FRAME, ASTACK in *; lia).
  assert (Hby : forall a, audio <= a < audio + NN -> ~ (spZ regs + -160 - 2 * ESTACK <= a < spZ regs + -160))
    by (intros a Ha; unfold ESTACK, DEC_CRT_STK, DEC_CRT_FRAME, ASTACK in *; lia).
  pose proof (amem_range_of_block segs B LAWS ly1 S1 W1 mem md R NN R NN HAR crtB_F_inR
    ltac:(lia) ltac:(lia)) as Hmx.
  pose proof (amem_range_of_block segs B LAWS ly1 S1 W1 mem md bA nA audio NN HAR crtB_F_inA
    HBA1 ltac:(lia)) as Hmy.
  pose proof (range_addressable_of_block segs B LAWS ly1 S1 W1 mem md R NN R NN HAR crtB_F_inR
    ltac:(lia) ltac:(lia)) as Hrx.
  pose proof (range_addressable_of_block segs B LAWS ly1 S1 W1 mem md bA nA audio NN HAR crtB_F_inA
    HBA1 ltac:(lia)) as Hry.
  assert (Hhx : 0 < NN -> shadow_hull_vis (aview segs (w_H W1) mem) R NN)
    by (intros Hn; exact (shadow_hull_vis_of_block segs B LAWS ly1 S1 W1 mem md R NN R NN HAR crtB_F_inR
          ltac:(lia) ltac:(lia) Hn)).
  assert (Hhy : 0 < NN -> shadow_hull_vis (aview segs (w_H W1) mem) audio NN)
    by (intros Hn; exact (shadow_hull_vis_of_block segs B LAWS ly1 S1 W1 mem md bA nA audio NN HAR crtB_F_inA
          HBA1 ltac:(lia) Hn)).
  assert (HRAW : YK0s.ret_ok (Z_to_bv 64 CRT_RET_BCMP))
    by (apply ret_ok_even; exact (proj2 (proj2 (proj2 crtB_pcs)))).
  eapply SRr_bind.
  { exact (@aj_bcmp_at fxc rc dec_B_sink_head segs B LAWS crtB_segs_low CRT_BCMP (RBC fxc) W1 regs4 mem
      DEC_CRT_STK (spZ regs) [] lyc Sc W memc mdc [] ly1 S1 md 3 R audio NN (-160) (Z_to_bv 64 CRT_RET_BCMP)
      HJ Ha0 Ha1 Ha2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
      Hsp eq_refl ltac:(lia) ltac:(unfold ESTACK, DEC_CRT_STK, DEC_CRT_FRAME, ASTACK; lia)
      (eq_trans E3 HGP) (eq_trans E4 HTP) Hra HRAW
      Hsx Hsy Hbx Hby Hmx Hmy Hrx Hhx Hry Hhy). }
  intros W2 c2 _ (-> & regs5 & mem5 & md5 & v & -> & HJ5 & HPR5 & Hv5 & Hiff & HK5 & HG5).
  assert (Hv0 : v = w64 0) by (apply Hiff; exact HEQ).
  assert (HROM5 : crtB_rom_on RO_RD W1 mem5).
  { apply (crtB_rom_keep W1 mem mem5 HROM). intros a Ha. pose proof (crtB_segs_low a Ha) as Hl.
    apply HK5; unfold ESTACK, DEC_CRT_STK, DEC_CRT_FRAME, ASTACK, kLowMemEnd in *; lia. }
  assert (HF5 : FRAMEOK mem5).
  { apply (crtB_F_frame_keep mem md mem5 HJ HF HG5). intros a Ha.
    apply HK5; unfold ESTACK, CRT_FRAME, DEC_CRT_STK, DEC_CRT_FRAME, ASTACK in *; lia. }
  exact (HB STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs audio pcm nch ns bA nA bP nP T ch
           ly1 S1 W1 mem5 md5 regs5 P Q R fxc v0 (w64 R) (w64 NN) v32 (w64 nch)
           HPRE (conj HJ5 (conj HFRS (conj HMO HROM5)))
           (crtB_regs_pres regs regs4 regs5 Q ns HREGS HPR5) (eq_trans Hv5 Hv0)
           (eq_trans (HPR5 8 ltac:(unfold acallee_saved; lia)) Hs0) HF5 HBL HFRM).
Qed.

(* ---- at CRT_RET_ENCODE: crt_seg6_F, then the bcmp call ---- *)
Lemma crtB_st_retenc : forall (fxc : YKK.FPState) (regs3 : bvmap 5 word) mem md,
  INNER mem md -> crtB_rom_on RO_RD W1 mem -> FRAMEOK mem -> crtB_regs regs regs3 Q ns ->
  YKK.getr regs3 8 = w64 R -> frm_zero (@fp_csr fxc) ->
  (forall i, 0 <= i < NN -> aview segs (w_H W1) mem (R + i) = aview segs (w_H W1) mem (audio + i)) ->
  SRr segs W1 (@cfg_at fxc segs CRT_RET_ENCODE regs3 mem md) POST.
Proof.
  intros fxc regs3 mem md HJ HROM HF HREGS Hs0 HFRM HEQ.
  destruct (crtB_F_stk mem md HJ) as (HAR & HPRES & Hc & H47).
  pose proof asan_consts as (AC & _).
  pose proof (crtB_F_esp regs3 mem md HJ HREGS) as ESP.
  pose proof HREGS as (E2 & E3 & E4 & E18 & E21 & E24).
  pose proof (crt_seg6_F (LCK.RNG_W (world segs) (@w_H segs) W1)
      (GR regs3 1) (GR regs3 2) (GR regs3 3) (GR regs3 4) (GR regs3 5) (GR regs3 6) (GR regs3 7)
      (GR regs3 8) (GR regs3 9) (GR regs3 10) (GR regs3 11) (GR regs3 12) (GR regs3 13) (GR regs3 14)
      (GR regs3 15) (GR regs3 16) (GR regs3 17) (GR regs3 18) (GR regs3 19) (GR regs3 20) (GR regs3 21)
      (GR regs3 22) (GR regs3 23) (GR regs3 24) (GR regs3 25) (GR regs3 26) (GR regs3 27) (GR regs3 28)
      (GR regs3 29) (GR regs3 30) (GR regs3 31)
      (@fp_regs fxc) (@fp_csr fxc) mem
      v0 (w64 R) (w64 NN) (w64 audio) v32 (w64 nch) (w64 P)
      (GR regs 27) (GR regs 26) (GR regs 25) (GR regs 24) (GR regs 23) (GR regs 22) (GR regs 21) (GR regs 20)
      (GR regs 19) (GR regs 18) (GR regs 9) (GR regs 8) (GR regs 1)
      ltac:(rewrite ESP; exact HF)
      ltac:(rewrite ESP; apply (crtB_rng_of_apresent W1 mem (spZ regs - CRT_FRAME) 160);
            [unfold CRT_FRAME, DEC_CRT_STK, DEC_CRT_FRAME, ASTACK in *; lia | unfold CRT_FRAME in *; lia
            | intros a Ha; apply HPRES; unfold CRT_FRAME, DEC_CRT_STK, DEC_CRT_FRAME, ASTACK in *; lia]))
    as HRUN.
  apply (@crtB_run fxc W1 regs3 mem md CRT_RET_ENCODE _ _ HRUN).
  intros ms' md' (ms0 & Hms0 & HEQV) HSBM. subst ms0.
  pose proof (fun (r : bv 5) (Hr : is_x0 r = false) => crtB_ms_reg _ _ _ _ _ _ _ _ r HEQV Hr) as GEQ.
  rewrite (@crtB_ms_shape fxc _ _ _ ms' HEQV).
  apply (crtB_st_bcmp fxc (ms_regs ms') mem md').
  - exact (crtB_aj_md mem md md' HJ HSBM).
  - exact HROM.
  - exact HF.
  - split; [exact (eq_trans (GEQ (Z_to_bv 5 2) eq_refl) E2)|].
    split; [exact (eq_trans (GEQ (Z_to_bv 5 3) eq_refl) E3)|].
    split; [exact (eq_trans (GEQ (Z_to_bv 5 4) eq_refl) E4)|].
    split; [exact (eq_trans (GEQ (Z_to_bv 5 18) eq_refl) E18)|].
    split; [exact (eq_trans (GEQ (Z_to_bv 5 21) eq_refl) E21)
           | exact (eq_trans (GEQ (Z_to_bv 5 24) eq_refl) E24)].
  - exact (GEQ (Z_to_bv 5 1) eq_refl).
  - exact (eq_trans (GEQ (Z_to_bv 5 8) eq_refl) Hs0).
  - exact (eq_trans (GEQ (Z_to_bv 5 10) eq_refl) Hs0).
  - exact (GEQ (Z_to_bv 5 11) eq_refl).
  - exact (GEQ (Z_to_bv 5 12) eq_refl).
  - exact HFRM.
  - exact HEQ.
Qed.

(* ---- at reac_braid_encode's entry: the leaf call ---- *)
Lemma crtB_st_enc : forall (fx1 : YKK.FPState) (regs2 : bvmap 5 word) mem1 md,
  INNER mem1 md -> crtB_rom_on RO_RD W1 mem1 -> FRAMEOK mem1 -> crtB_regs regs regs2 Q ns ->
  YKK.getr regs2 1 = Z_to_bv 64 CRT_RET_ENCODE -> YKK.getr regs2 8 = w64 R ->
  YKK.getr regs2 10 = w64 R -> YKK.getr regs2 11 = w64 nch -> YKK.getr regs2 12 = w64 Q ->
  YKK.getr regs2 13 = w64 nch -> YKK.getr regs2 14 = w64 ns ->
  frm_zero (@fp_csr fx1) ->
  crtB_conv (aview segs (w_H W) memc) pcm nch ns P Q mem1 ->
  SRr segs W1 (mkCfg (@YKK.mkst fx1 regs2 (Z_to_bv 64 CRT_ENCODE) mem1 (YKK.seg_rom segs)) md) POST.
Proof.
  intros fx1 regs2 mem1 md HJ HROM HF HREGS Hra Hs0 Ha0 Ha1 Ha2 Ha3 Ha4 HFRM HCONV.
  pose proof crtB_F_num as (HN & HNS & HKB & HEV).
  pose proof HPRE as (_ & _ & _ & HGP & HTP & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HINA & HBA1 & HBA2 &
                      _ & _ & _ & HBR & _).
  pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & HKB0 & _ & _ & _ & HPRES & _ & _ & HQT).
  destruct (crtB_F_stk mem1 md HJ) as (_ & _ & Hc & H47).
  pose proof asan_consts as (AC & _ & HKM & HKE & HKL).
  pose proof (crtB_F_esp regs2 mem1 md HJ HREGS) as ESP.
  pose proof HREGS as (E2 & E3 & E4 & E18 & E21 & E24).
  destruct (crtB_blk LAWS _ _ _ _ _ _ _ HAR crtB_F_inR) as (R16 & R4096 & Rn0 & Rnq & Rc & Rapp & RB).
  destruct (crtB_blk LAWS _ _ _ _ _ _ _ HAR crtB_F_inQ) as (Q16 & Q4096 & Qn0 & Qnq & Qc & Qapp & QB).
  destruct (crtB_blk LAWS _ _ _ _ _ _ _ HAR crtB_F_inP) as (P16 & P4096 & Pn0 & Pnq & Pc & Papp & PB).
  destruct (crtB_blk LAWS _ _ _ _ _ _ _ HAR crtB_F_inA) as (A16 & A4096 & An0 & Anq & Ac & Aapp & AB).
  destruct (crtB_F_sep mem1 md HAR) as (DRQ & DRP & DRA & HRnot).
  destruct HCONV as (HCQ & HCP).
  pose proof crtB_img_bounds as (I0 & I1 & I2).
  assert (HNN : 0 < NN <= 1440) by nia.
  assert (HN3 : 3 * nch * ns = NN) by ring.
  assert (HBA2' : audio + NN <= bA + nA) by nia.
  set (rd0 := aview segs (w_H W) memc) in *.
  set (Qf := fun c => P + 4 * (c * ns)).
  set (Kf := fun s c => crtB_s24 (crtB_pb rd0 pcm (3 * (c * ns + s))) (crtB_pb rd0 pcm (3 * (c * ns + s) + 1))
                                 (crtB_pb rd0 pcm (3 * (c * ns + s) + 2))).
  set (Vf := fun s c => crtB_cv rd0 pcm (c * ns + s)).
  assert (HFRAME : BN.REAC_BRAID_ENCODE_FRAME = 128) by reflexivity.
  (* the leaf's premises, in its order *)
  assert (HEC : LCK.ecall_pre (world segs) (@w_H segs) alayout astate (@AR rc segs B) ly_stk_lo ly_stk_hi
                  YK0s.ret_ok (as_gp B) (as_tp B) ly1 S1 W1 regs2 mem1 md).
  { exact (@ecall_pre_at rc dec_B_sink_head segs B DEC_CRT_STK (spZ regs) [] lyc Sc W memc mdc [] ly1 S1 W1 mem1 md 3
      regs2 (-160) HJ
      ltac:(unfold spZ at 1; change (YKK.getr regs2 2) with (GR regs2 2); rewrite ESP; unfold CRT_FRAME; lia)
      eq_refl ltac:(lia) ltac:(unfold ESTACK, DEC_CRT_STK, DEC_CRT_FRAME, ASTACK; lia)
      ltac:(rewrite Hra; apply ret_ok_even; exact (proj1 (proj2 (proj2 crtB_pcs))))
      (eq_trans E3 HGP) (eq_trans E4 HTP)). }
  assert (P11 : stk rsegs mem1 (bv_unsigned (GR regs2 2) - BN.REAC_BRAID_ENCODE_FRAME) (bv_unsigned (GR regs2 2))).
  { rewrite ESP, HFRAME. apply (crtB_stk_of (w_H W1));
      [unfold CRT_FRAME, DEC_CRT_STK, DEC_CRT_FRAME, ASTACK in *; lia | unfold CRT_FRAME in *; lia |].
    intros a Ha. apply HPRES. unfold CRT_FRAME, DEC_CRT_STK, DEC_CRT_FRAME, ASTACK in *; lia. }
  assert (P13 : R + 3 * nch * ns <= 2 ^ 64) by lia.
  assert (P14 : wr_at rsegs mem1 R (3 * nch * ns)).
  { apply (crtB_wr_at_of (w_H W1)); [lia | lia |]. intros a Ha. exact (proj1 (RB a ltac:(lia))). }
  assert (PQm8 : Q mod 8 = 0) by (Z.div_mod_to_equations; lia).
  assert (P19 : forall c, 0 <= c < nch -> 0 < Qf c /\ Qf c mod 4 = 0 /\ Qf c + 4 * ns <= 2 ^ 64).
  { intros c Hc'. unfold Qf. split; [nia|]. split; [|nia].
    replace (P + 4 * (c * ns)) with (P + (c * ns) * 4) by ring. rewrite Z.mod_add by lia.
    Z.div_mod_to_equations; lia. }
  assert (P20 : forall s c, 0 <= s < ns -> 0 <= c < nch ->
    bytes_at rsegs mem1 (Qf c + 4 * s) (le4 (Z_to_bv 64 (Vf s c))) /\ RBr.rb_sample (Vf s c) (Kf s c)).
  { intros s c Hs Hc'.
    assert (HS : RBr.rb_sample (Vf s c) (Kf s c)).
    { unfold RBr.rb_sample, Vf, Kf, crtB_cv. split; [apply crtB_s24_rng; apply crtB_pb_rng|]. left. reflexivity. }
    split; [|exact HS].
    destruct (RBL.rbe_pipe _ _ HS) as (HV & _).
    unfold le4. rewrite (unsigned_lit (Vf s c)) by lia.
    replace (Qf c + 4 * s) with (P + 4 * (c * ns + s)) by (unfold Qf; ring).
    exact (HCP (c * ns + s) ltac:(nia)). }
  assert (P21 : R + 3 * nch * ns <= Q \/ Q + 8 * nch <= R) by lia.
  assert (P22 : forall c, 0 <= c < nch -> R + 3 * nch * ns <= Qf c \/ Qf c + 4 * ns <= R)
    by (intros c Hc'; unfold Qf; nia).
  assert (P23 : R + 3 * nch * ns <= bv_unsigned (GR regs2 2) - BN.REAC_BRAID_ENCODE_FRAME \/
                bv_unsigned (GR regs2 2) <= R)
    by (rewrite ESP, HFRAME; left; unfold CRT_FRAME, DEC_CRT_STK, DEC_CRT_FRAME, ASTACK in *; lia).
  assert (P24 : Q + 8 * nch <= bv_unsigned (GR regs2 2) - BN.REAC_BRAID_ENCODE_FRAME \/
                bv_unsigned (GR regs2 2) <= Q)
    by (rewrite ESP, HFRAME; left; unfold CRT_FRAME, DEC_CRT_STK, DEC_CRT_FRAME, ASTACK in *; lia).
  assert (P25 : forall c, 0 <= c < nch -> Qf c + 4 * ns <= bv_unsigned (GR regs2 2) - BN.REAC_BRAID_ENCODE_FRAME \/
                bv_unsigned (GR regs2 2) <= Qf c)
    by (intros c Hc'; rewrite ESP, HFRAME; left; unfold Qf, CRT_FRAME, DEC_CRT_STK, DEC_CRT_FRAME, ASTACK in *; nia).
  assert (P26 : BC.asan_cells mem1) by exact (dec_cells_asan B HCELLS ly1 S1 W1 mem1 md (w_Hoff W1) HAR).
  assert (P28 : BC.addressable mem1 R (3 * nch * ns))
    by exact (crtB_addr LAWS ly1 S1 W1 mem1 md R NN R (3 * nch * ns) HAR crtB_F_inR ltac:(lia) ltac:(lia) ltac:(lia)).
  assert (P29 : BC.addressable mem1 Q (8 * nch))
    by exact (crtB_addr LAWS ly1 S1 W1 mem1 md Q (8 * nch) Q (8 * nch) HAR crtB_F_inQ ltac:(lia) ltac:(lia) ltac:(lia)).
  assert (P30 : forall c, 0 <= c < nch -> BC.addressable mem1 (Qf c) (4 * ns)).
  { intros c Hc'. exact (crtB_addr LAWS ly1 S1 W1 mem1 md P (4 * (nch * ns)) (Qf c) (4 * ns) HAR crtB_F_inP
      ltac:(unfold Qf; nia) ltac:(unfold Qf; nia) ltac:(lia)). }
  assert (P31 : forall x, BC.GOT_CELL_K <= x < BC.GOT_CELL_K + 8 \/ BC.CELL_K <= x < BC.CELL_K + 8 \/
      BC.in_shadow x ->
      outside [(bv_unsigned (GR regs2 2) - BN.REAC_BRAID_ENCODE_FRAME, bv_unsigned (GR regs2 2));
               (R, R + 3 * nch * ns)] x).
  { intros x Hx. rewrite ESP, HFRAME.
    assert (Hcells : (BC.GOT_CELL_K <= x < BC.GOT_CELL_K + 8 \/ BC.CELL_K <= x < BC.CELL_K + 8) ->
                     in_img segs x).
    { intros Hc'. apply crtB_in_img_of. rewrite YImgTop.IMG_LO_val, YImgTop.IMG_TOP_val.
      unfold BC.GOT_CELL_K, BC.CELL_K in *. lia. }
    cbn [outside]. split; [|split; [|exact I]].
    - unfold CRT_FRAME, DEC_CRT_STK, DEC_CRT_FRAME, ASTACK, BC.GOT_CELL_K, BC.CELL_K, BC.in_shadow,
        BC.LOWMEM_END, BC.LOWSHADOW_END, BC.HIGHSHADOW_BEG, BC.HIGHMEM_BEG in *. lia.
    - intros Hr. destruct Hx as [Hx|[Hx|Hx]].
      + exact (proj2 (proj2 (RB x ltac:(lia))) (Hcells (or_introl Hx))).
      + exact (proj2 (proj2 (RB x ltac:(lia))) (Hcells (or_intror Hx))).
      + unfold BC.in_shadow, BC.LOWMEM_END, BC.LOWSHADOW_END, BC.HIGHSHADOW_BEG, BC.HIGHMEM_BEG in Hx.
        destruct Rapp as [Rp4096 [HL | [HH1 HH2]]]; unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia. }
  (* the read-only premises: mrd is the ROM over the leaf's read-only set, which is off its frame *)
  assert (PRO : forall x : word, (exists r, In r LBraidB.REAC_BRAID_ENCODE_RO_RD /\ fst r <= bv_unsigned x < fst r + snd r) ->
                  mrd rsegs mem1 x = seg_rom rsegs x).
  { intros x Hx. exact (crtB_ls_ro W1 mem1 HROM x (HRO_SUB _ Hx) (crtB_braid_ro_rom _ Hx)). }
  assert (PROF : forall x, (exists r, In r LBraidB.REAC_BRAID_ENCODE_RO_RD /\ fst r <= x < fst r + snd r) ->
                   outside [(bv_unsigned (GR regs2 2) - BN.REAC_BRAID_ENCODE_FRAME, bv_unsigned (GR regs2 2))] x).
  { intros x Hx. pose proof (crtB_ls_frame_off mem1 md HJ x Hx) as Hoff. rewrite ESP, HFRAME.
    cbn [outside]. split; [|exact I]. intros Hw. apply Hoff.
    unfold CRT_FRAME, DEC_CRT_STK, DEC_CRT_FRAME, ASTACK in *. lia. }
  (* the image words the leaf reads are visible *)
  assert (HIMGV : forall lo n, YImgTop.IMG_LO <= lo -> lo + n <= YImgTop.IMG_TOP ->
                    ExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W1) lo n).
  { intros lo n H1 H2. apply crtB_rng_of_vis; [lia | unfold kLowMemEnd in I2; lia |].
    intros a Ha. apply crtB_img_vis. lia. }
  assert (PGOT : ExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W1) BC.GOT_CELL_K 8).
  { apply HIMGV; rewrite ?YImgTop.IMG_LO_val, ?YImgTop.IMG_TOP_val; unfold BC.GOT_CELL_K; lia. }
  assert (PCELL : ExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W1) BC.CELL_K 8).
  { apply HIMGV; rewrite ?YImgTop.IMG_LO_val, ?YImgTop.IMG_TOP_val; unfold BC.CELL_K; lia. }
  assert (PROR : ExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W1)
                   (fst (hd (0, 0) LBraidB.REAC_BRAID_ENCODE_RO_RD)) (snd (hd (0, 0) LBraidB.REAC_BRAID_ENCODE_RO_RD))).
  { apply HIMGV; rewrite ?YImgTop.IMG_LO_val, ?YImgTop.IMG_TOP_val; unfold LBraidB.REAC_BRAID_ENCODE_RO_RD;
      cbn [hd fst snd]; lia. }
  assert (P33 : ExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W1)
                  (bv_unsigned (GR regs2 2) - BN.REAC_BRAID_ENCODE_FRAME) BN.REAC_BRAID_ENCODE_FRAME).
  { rewrite ESP, HFRAME. apply (crtB_rng_of_apresent W1 mem1);
      [unfold CRT_FRAME, DEC_CRT_STK, DEC_CRT_FRAME, ASTACK in *; lia | unfold CRT_FRAME in *; lia |].
    intros a Ha. apply HPRES. unfold CRT_FRAME, DEC_CRT_STK, DEC_CRT_FRAME, ASTACK in *; lia. }
  assert (P34 : ExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W1) R (3 * nch * ns)).
  { apply (crtB_rng_of_apresent W1 mem1); [lia | lia |]. intros a Ha. exact (proj1 (RB a ltac:(lia))). }
  assert (P35 := crtB_rng_hull W1 mem1 R (3 * nch * ns) ltac:(lia) ltac:(lia) ltac:(lia)
    (shadow_hull_vis_of_block segs B LAWS ly1 S1 W1 mem1 md R NN R (3 * nch * ns) HAR crtB_F_inR
       ltac:(lia) ltac:(lia) ltac:(lia))).
  assert (P36 : ExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W1) Q (8 * nch)).
  { apply (crtB_rng_of_apresent W1 mem1); [lia | lia |]. intros a Ha. exact (proj1 (QB a ltac:(lia))). }
  assert (P37 := crtB_rng_hull W1 mem1 Q (8 * nch) ltac:(lia) ltac:(lia) ltac:(lia)
    (shadow_hull_vis_of_block segs B LAWS ly1 S1 W1 mem1 md Q (8 * nch) Q (8 * nch) HAR crtB_F_inQ
       ltac:(lia) ltac:(lia) ltac:(lia))).
  assert (P38 : forall c, 0 <= c < nch -> ExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W1) (Qf c) (4 * ns)).
  { intros c Hc'. apply (crtB_rng_of_apresent W1 mem1); [unfold Qf; nia | unfold Qf; nia |].
    intros a Ha. unfold Qf in Ha. exact (proj1 (PB a ltac:(nia))). }
  assert (P39 : forall c, 0 <= c < nch ->
    ExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W1) (BC.shadow_addr (Qf c) / 8 * 8)
      (BC.shadow_addr (Qf c + 4 * ns - 1) / 8 * 8 + 8 - BC.shadow_addr (Qf c) / 8 * 8)).
  { intros c Hc'. apply (crtB_rng_hull W1 mem1 (Qf c) (4 * ns)); [unfold Qf; nia | unfold Qf; nia | lia |].
    exact (shadow_hull_vis_of_block segs B LAWS ly1 S1 W1 mem1 md P (4 * (nch * ns)) (Qf c) (4 * ns) HAR crtB_F_inP
       ltac:(unfold Qf; nia) ltac:(unfold Qf; nia) ltac:(lia)). }
  assert (P40 : forall x, LeafCgKit.in_wr [(R, R + 3 * nch * ns)] x -> ~ aowned B ly1 S1 x /\ ~ LeafCgKit.in_img x).
  { intros x Hx. apply crtB_in_wr1 in Hx. destruct (RB x ltac:(lia)) as (_ & Ho & Hi).
    split; [exact Ho | exact Hi]. }
  (* the leaf call *)
  rewrite crtB_enc_pc.
  eapply SRr_bind.
  { exact (REL fx1 ly1 S1 W1 regs2 mem1 md R nch Q ns Qf Vf Kf HEC Ha0 Ha1 Ha2 Ha3 Ha4 HN HEV HNS HFRM PRO PROF
      P11 ltac:(lia) P13 P14 ltac:(lia) PQm8 ltac:(lia) HCQ P19 P20 P21 P22 P23 P24 P25 P26 P28 P29 P30 P31
      PGOT PCELL PROR P33 P34 P35 P36 P37 P38 P39 P40). }
  intros W' c' _ HPOST.
  destruct HPOST as (-> & fx' & regs3 & mem3 & md3 & -> & Hcsr & _ & HAR3 & HPR3 & HSB3 & HK3 & HG3 & HX3).
  assert (Era : LCK.w64 (LCK.raZ regs2) = Z_to_bv 64 CRT_RET_ENCODE).
  { unfold LCK.w64, LCK.raZ. change (YKK.getr regs2 (Z_to_bv 5 1)) with (YKK.getr regs2 1). rewrite Hra.
    rewrite unsigned_lit by exact (proj1 crtB_pcs). reflexivity. }
  rewrite Era.
  (* the inner journal after the leaf: it wrote its stack window and R *)
  assert (HKEEP : forall a, 0 <= a < 2 ^ 64 ->
      ~ ((spZ regs - CRT_FRAME - ESTACK <= a < spZ regs - CRT_FRAME) \/ (R <= a < R + NN)) ->
      aview segs (w_H W1) mem3 a = aview segs (w_H W1) mem1 a).
  { intros a Ha HW. apply HK3; [exact Ha | |].
    - unfold LCK.spZ, LCK.ESTACK. rewrite ESP. intros Hw. apply HW. left. unfold ESTACK. lia.
    - apply crtB_not_in_wr. intros Hr. apply HW. right. lia. }
  assert (HJ3 : INNER mem3 md3).
  { assert (HWB : forall a, ((spZ regs - CRT_FRAME - ESTACK <= a < spZ regs - CRT_FRAME) \/ (R <= a < R + NN)) ->
        awr_byte DEC_CRT_STK (spZ regs) [] (ablocks B lyc Sc) (ablocks B ly1 S1) ly1 [] a \/
        (aowned B ly1 S1 a /\ app_addr a /\ ~ in_img segs a)).
    { intros a [Ha|Ha]; left; unfold awr_byte.
      - left. unfold CRT_FRAME, ESTACK, DEC_CRT_STK, DEC_CRT_FRAME, ASTACK in *. lia.
      - right. right. left. exists R, NN. split; [exact crtB_F_inR|]. split; [exact HRnot | lia]. }
    assert (HGROW : forall a, apresent (w_H W1) mem1 a -> apresent (w_H W1) mem3 a) by exact HG3.
    eapply ajournal_after_write with
      (Wr := fun a => (spZ regs - CRT_FRAME - ESTACK <= a < spZ regs - CRT_FRAME) \/ (R <= a < R + NN))
      (S' := S1) (own2 := []);
      solve [ exact LAWS | exact crtB_segs_low | exact HJ | exact HKEEP | exact HGROW | exact HSB3 | exact HWB
            | exact HAR3 | reflexivity | lia | exact HFRS | exact HQT ]. }
  assert (HROM3 : crtB_rom_on RO_RD W1 mem3).
  { apply (crtB_rom_keep W1 mem1 mem3 HROM). intros a Ha. pose proof (crtB_segs_low a Ha) as Hl.
    apply HKEEP; [unfold kLowMemEnd in Hl; lia|].
    intros [Hw|Hr]; [unfold CRT_FRAME, ESTACK, DEC_CRT_STK, DEC_CRT_FRAME, ASTACK, kLowMemEnd in *; lia|].
    exact (proj2 (proj2 (RB a ltac:(lia))) Ha). }
  assert (HF3 : FRAMEOK mem3).
  { apply (crtB_F_frame_keep mem1 md mem3 HJ HF HG3). intros a Ha. apply HKEEP; [unfold CRT_FRAME, DEC_CRT_STK, DEC_CRT_FRAME, ASTACK in *; lia|].
    intros [Hw|Hr]; unfold CRT_FRAME, ESTACK, DEC_CRT_STK, DEC_CRT_FRAME, ASTACK in *; lia. }
  (* the braid: R now holds the caller's audio *)
  assert (HEQ3 : forall i, 0 <= i < NN -> aview segs (w_H W1) mem3 (R + i) = aview segs (w_H W1) mem3 (audio + i)).
  { intros i Hi.
    destruct (CE.rb_cover nch ns i ltac:(lia) HEV ltac:(lia) ltac:(lia)) as (s & c & j & Hs & Hc' & Hj & Ei).
    assert (HA3 : aview segs (w_H W1) mem3 (audio + i) = rd0 (audio + i)).
    { rewrite HKEEP by (first [lia | intros [Hw|Hr]; unfold CRT_FRAME, ESTACK, DEC_CRT_STK, DEC_CRT_FRAME, ASTACK in *; lia]).
      replace (audio + i) with (bA + (audio + i - bA)) by ring.
      apply (HKB0 bA nA (audio + i - bA) HINA crtB_F_inA ltac:(lia)).
      intros (r & Hr & _). destruct Hr. }
    destruct (HBR c s j Hc' Hs Hj) as (b & Hb1 & Hb2).
    assert (EA : audio + i = audio + 3 * (s * nch + 2 * (c / 2)) + DCBc.braid_off c j).
    { rewrite Ei, <- (crtB_braid_off_at nch s c j ltac:(lia) Hj). ring. }
    rewrite HA3, EA, Hb2.
    assert (Hvis : w_H W1 (wa (R + i)) = false) by exact (proj1 (proj1 (RB (R + i) ltac:(lia)))).
    rewrite (crtB_aview_mrd (w_H W1) mem3 (R + i) Hvis).
    unfold mrd. rewrite (HX3 (wa (R + i))).
    2: { rewrite wa_unsigned by lia. cbn [outside]. split; [|exact I].
         change (YK11.getr regs2 (Z_to_bv 5 2)) with (GR regs2 2). rewrite ESP, HFRAME.
         unfold CRT_FRAME, DEC_CRT_STK, DEC_CRT_FRAME, ASTACK in *. lia. }
    rewrite Ei.
    rewrite (CE.rb_rows_at R nch Kf (Z.to_nat ns) mem1 s c j ltac:(lia) ltac:(lia) HEV
               ltac:(rewrite Z2Nat.id by lia; nia) ltac:(rewrite Z2Nat.id by lia; lia) Hc' Hj).
    cbv beta iota. cbn [option_map]. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    unfold Kf. cbv beta.
    rewrite crtB_s24_byte by (first [apply crtB_pb_rng | exact Hj]).
    assert (Hpb : crtB_pb rd0 pcm (3 * (c * ns + s) + j) = b).
    { unfold crtB_pb. replace (pcm + (3 * (c * ns + s) + j)) with (pcm + 3 * (c * ns + s) + j) by ring.
      rewrite Hb1. reflexivity. }
    assert (Cj : j = 0 \/ j = 1 \/ j = 2) by lia.
    destruct Cj as [-> | [-> | ->]]; cbn [Z.eqb Pos.eqb]; [rewrite Z.add_0_r in Hpb|..]; exact Hpb. }
  apply (crtB_st_retenc fx' regs3 mem3 md3 HJ3 HROM3 HF3).
  - exact (crtB_regs_pres regs regs2 regs3 Q ns HREGS HPR3).
  - exact (eq_trans (HPR3 8 ltac:(unfold LCK.acallee_saved; lia)) Hs0).
  - unfold frm_zero. rewrite Hcsr. exact HFRM.
  - exact HEQ3.
Qed.

(* ---- at CRT_LOOP_OUT: crt_seg5_F, then the leaf call ---- *)
Lemma crtB_st_loopout : forall (fx1 : YKK.FPState) (regs1 : bvmap 5 word) mem1 md1,
  INNER mem1 md1 -> crtB_rom_on RO_RD W1 mem1 -> FRAMEOK mem1 -> crtB_regs regs regs1 Q ns ->
  frm_zero (@fp_csr fx1) -> crtB_conv (aview segs (w_H W) memc) pcm nch ns P Q mem1 ->
  SRr segs W1 (@cfg_at fx1 segs CRT_LOOP_OUT regs1 mem1 md1) POST.
Proof using All.
  intros fx1 regs1 mem1 md1 HJ HROM HF HREGS HFRM HCONV.
  destruct (crtB_F_stk mem1 md1 HJ) as (HAR & HPRES & Hc & H47).
  pose proof asan_consts as (AC & _).
  pose proof (crtB_F_esp regs1 mem1 md1 HJ HREGS) as ESP.
  pose proof HREGS as (E2 & E3 & E4 & E18 & E21 & E24).
  pose proof (crt_seg5_F (LCK.RNG_W (world segs) (@w_H segs) W1)
      (GR regs1 1) (GR regs1 2) (GR regs1 3) (GR regs1 4) (GR regs1 5) (GR regs1 6) (GR regs1 7)
      (GR regs1 8) (GR regs1 9) (GR regs1 10) (GR regs1 11) (GR regs1 12) (GR regs1 13) (GR regs1 14)
      (GR regs1 15) (GR regs1 16) (GR regs1 17) (GR regs1 18) (GR regs1 19) (GR regs1 20) (GR regs1 21)
      (GR regs1 22) (GR regs1 23) (GR regs1 24) (GR regs1 25) (GR regs1 26) (GR regs1 27) (GR regs1 28)
      (GR regs1 29) (GR regs1 30) (GR regs1 31)
      (@fp_regs fx1) (@fp_csr fx1) mem1
      v0 (w64 R) (w64 NN) (w64 audio) v32 (w64 nch) (w64 P)
      (GR regs 27) (GR regs 26) (GR regs 25) (GR regs 24) (GR regs 23) (GR regs 22) (GR regs 21) (GR regs 20)
      (GR regs 19) (GR regs 18) (GR regs 9) (GR regs 8) (GR regs 1)
      ltac:(rewrite ESP; exact HF)
      ltac:(rewrite ESP; apply (crtB_rng_of_apresent W1 mem1 (spZ regs - CRT_FRAME) 160);
            [unfold CRT_FRAME, DEC_CRT_STK, DEC_CRT_FRAME, ASTACK in *; lia | unfold CRT_FRAME in *; lia
            | intros a Ha; apply HPRES; unfold CRT_FRAME, DEC_CRT_STK, DEC_CRT_FRAME, ASTACK in *; lia]))
    as HRUN.
  apply (@crtB_run fx1 W1 regs1 mem1 md1 CRT_LOOP_OUT _ _ HRUN).
  intros ms' md' (ms0 & Hms0 & HEQV) HSBM. subst ms0.
  pose proof (fun (r : bv 5) (Hr : is_x0 r = false) => crtB_ms_reg _ _ _ _ _ _ _ _ r HEQV Hr) as GEQ.
  rewrite (@crtB_ms_shape fx1 _ _ _ ms' HEQV).
  apply (crtB_st_enc fx1 (ms_regs ms') mem1 md').
  - exact (crtB_aj_md mem1 md1 md' HJ HSBM).
  - exact HROM.
  - exact HF.
  - split; [exact (eq_trans (GEQ (Z_to_bv 5 2) eq_refl) E2)|].
    split; [exact (eq_trans (GEQ (Z_to_bv 5 3) eq_refl) E3)|].
    split; [exact (eq_trans (GEQ (Z_to_bv 5 4) eq_refl) E4)|].
    split; [exact (eq_trans (GEQ (Z_to_bv 5 18) eq_refl) E18)|].
    split; [exact (eq_trans (GEQ (Z_to_bv 5 21) eq_refl) E21)
           | exact (eq_trans (GEQ (Z_to_bv 5 24) eq_refl) E24)].
  - exact (GEQ (Z_to_bv 5 1) eq_refl).
  - exact (GEQ (Z_to_bv 5 8) eq_refl).
  - exact (GEQ (Z_to_bv 5 10) eq_refl).
  - exact (GEQ (Z_to_bv 5 11) eq_refl).
  - exact (eq_trans (GEQ (Z_to_bv 5 12) eq_refl) E21).
  - exact (GEQ (Z_to_bv 5 13) eq_refl).
  - exact (eq_trans (GEQ (Z_to_bv 5 14) eq_refl) E18).
  - exact HFRM.
  - exact HCONV.
Qed.
End Fixed.

(* The piece for any read-only set RO_RD that holds the braid leaf's read-only read set (HRO_SUB); crtB_encbcmp below
   instantiates RO_RD by the statement's DEC_RO_RD, where HRO_SUB is decided. *)
Theorem crtB_encbcmp_sub : crtB_encbcmp_stmt B MT RO_RD.
Proof.
  intros RU HB.
  destruct RU as (_ & _ & HCELLS & LAWS & _ & _ & _ & _ & _ & RBC & REL).
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs audio pcm nch ns bA nA bP nP T ch
         ly1 S1 W1 mem1 md1 regs1 P Q R fx1 v0 v32 HPRE HMID HREGS HFR HBL HFRM HCONV.
  destruct HMID as (HJ & HFRS & HMO & HROM).
  exact (crtB_st_loopout STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs audio pcm nch ns bA nA bP nP T ch
           ly1 S1 W1 P Q R v0 v32 LAWS HCELLS RBC REL HB HPRE HFRS HMO HBL fx1 regs1 mem1 md1
           HJ HROM HFR HREGS HFRM HCONV).
Qed.
End EncBcmp.

(* REAC_BRAID_ENCODE_RO_RD (the braid leaf's read-only read set) is a sub-list of the statement's DEC_RO_RD. *)
Lemma crtB_braid_ro_sub_b :
  forallb (fun r => existsb (fun r' => (fst r =? fst r') && (snd r =? snd r'))%bool DEC_RO_RD)
    LBraidB.REAC_BRAID_ENCODE_RO_RD = true.
Proof. vm_compute. reflexivity. Qed.

Lemma crtB_braid_ro_sub_dec : forall a,
  (exists r, In r LBraidB.REAC_BRAID_ENCODE_RO_RD /\ fst r <= a < fst r + snd r) -> crtB_in_ro_rd DEC_RO_RD a.
Proof.
  intros a (r & Hr & Ha). pose proof crtB_braid_ro_sub_b as C. rewrite forallb_forall in C.
  specialize (C r Hr). apply existsb_exists in C as (r' & Hr' & Hb).
  apply andb_prop in Hb as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2.
  exists r'. split; [exact Hr' | rewrite <- H1, <- H2; exact Ha].
Qed.

Section Close.
Context {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.

(* The piece, at the statement's read-only set DEC_RO_RD (the set the close instantiates crtB_cuts' RO_RD by). *)
Theorem crtB_encbcmp : crtB_encbcmp_stmt B MT DEC_RO_RD.
Proof.
  apply (crtB_encbcmp_sub B MT DEC_RO_RD). exact crtB_braid_ro_sub_dec.
Qed.
End Close.
