(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/ProgWorldShadow.v (a working branch
   516f9e5a3d1, re-synced to a working branch 1d23ced37fd (= a working branch 1888d8b45bf): A's twin-module
   comment above the Requires, Lib.Mem by its core path, and the global-shadow lemmas ctl_gshadow_of_AR_fixed /
   pwsh_addressable_app / ctl_global_shadow_of_AR_fixed, all of which B takes, under the same names; then to
   a working branch fec8db0a380 (A's file from a Theorem Labs lane 87ed4849733): the two global-shadow lemmas take
   ProgWorld's names, ctl_gshadow_of_AR / ctl_global_shadow_of_AR, stated as B.ProgWorld.ctl_gshadow_of_AR_stmt B /
   ctl_global_shadow_of_AR_stmt B (the same texts as the _fixed statements; the same proofs), and YP09 joins the
   YK11 YM05 Require line, as A; then to a working branch 0e97fddfcea (A blob a10a774a57e): ctl_const_vis_of_AR,
   B.ProgWorld.ctl_const_vis_of_AR_stmt B with A's proof, and A's added Require line for ProgWorld_Fs / ProgWorldVisFrame):
   lib.A.ProgWorld -> lib.B.ProgWorld, lib.A.AsanRT -> lib.B.AsanRT, lib.A.Img0 -> lib.B.Img0, lib.A.AF0m ->
   lib.Reusable.YF0m (CtrlTSyms, ts_const, Tfib_const = Tfib_const_sym ++ Tfib_const_abs ++ Tfib_const_shadow, the
   last being a Theorem Labs lane's global-shadow rows of record for image B),
   lib.A.AB1v -> lib.Reusable.YB1v (segs = YB1v.tfibsegs = AsanUbsan.M.loaded_segments = B.Img0.rsegs,
   lib/B/ProgBridge.v tfibsegs_rsegs).  The core files this proof reads (lib/Reusable/YG0d, YG0f, YG0n, YG00,
   YG0v, YA0n, YK04, YK11, YM05, YP09) are byte-identical to the ones the A file reads, so every proof step is
   A's.  No image constant is written here: the proof names B's by B.AsanRT.ASAN_K / LOWMEM_END / HIGHMEM_BEG /
   APPMEM_END / shadow_addr / shadow_ok / app_mem / addr_byte / addressable (lib/B/AsanRT.v:8-23).  Its only
   literals are image-independent: 8 and 7 (ASan's shadow granule and its partial-granule bound, the same in
   both images) and 128 = bv_half_modulus 8 (the byte's signed wrap point).
   Two of the core modules this file names, YK11 and YM05, exist twice (lib/Reusable and lib/B/Reusable).  Their
   uses keep A's spelling `lib.Reusable.<X>.<name>` (the CORE copy, which passes the record core's six-module
   gate, porter 04:25Z), and their Require line is A's (`From ...fuzz_ctrl.lib.Reusable Require YK11 YM05 YP09`;
   YP09 is also lib/B/Reusable/YP09.v); Mem is Required as A Requires it (`From ...fuzz_ctrl.lib.Lib Require Mem`,
   uses lib.Lib.Mem).  Locate confirms
   every name here resolves under lib.Reusable, never lib.B.Reusable.  The global-shadow lemmas' constants are
   image-independent and named, as in A: B.AsanRT.ASAN_K = lib.Reusable.YG0f.SHADOW_OFF = 0x7fff8000,
   B.AsanRT.LOWMEM_END, APPMEM_END (lib/B/AsanRT.v:8-13, the same values as lib/A/AsanRT.v) and the core's kImgLo /
   kImgEnd (lib/Reusable/YG0f.v:19-20).  *)
(* lib/B/ProgWorldShadow.v -- fuzz_ctrl image B (asan-ubsan, libreac v1.9.0): the three statements of
   lib/B/ProgWorld.v Section BlkShadow, proved.  proves no function (kind: segment lemma).

   ctl_block_shadow_of_AR: every byte of a sub-range of a live block (p, n) is B.AsanRT.addressable.  Source: the
   core's AR_shadow_law (YG0d.v:430-434: block_shadow of the view at p for req_size n bytes, i.e. shadow 0 over the
   full granules and req_size n mod 8 over the last partial one) and AR_blocks_law (:423-429: p + req_size n <=
   alloc_ceiling, in_app).  ctl_zshadow_of_AR: the same for a sub-range of the full granules of an as_zero_shadow
   range.  Source: AR_zshadow_law (:435-438) and asyms_ok's aso_zshadow (YG0f.v:191: 8-aligned, below kLowMemEnd).
   Both turn the view's shadow value into ctrl's mrd by pwsh_view_mrd: at a visible address that is
   ProgWorld.aview_vis_mrd; a hidden address lies off every segment (w_Hoff), so its view is None (YK04.v:166). *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
(* Twin modules (YI04 YI16 YK11 YK1b YM05 YO09) by their CORE path, and every use below is lib.Reusable.X (porter 04:24Z / 04:33Z). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YM05 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YG00 Reusable.YG0f.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0n Reusable.YG0d Reusable.YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YB1v B.AsanRT B.Img0 Reusable.YF0m B.ProgWorld.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ProgWorld_Fs B.ProgWorldVisFrame.
(* lib/Lib also has unit copies (lib/B/Bz/Lib/...): Mem by its core path, uses spelled lib.Lib.Mem.X. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem.
Local Open Scope Z_scope.

Notation segs := lib.Reusable.YB1v.tfibsegs (only parsing).

Section Shadow.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : lib.Reusable.YG0f.asyms.

Lemma pwsh_byte_signed_small : forall b : byte, bv_unsigned b < 128 -> bv_signed b = bv_unsigned b.
Proof.
  intros b H. pose proof (bv_unsigned_in_range 8 b) as R.
  unfold bv_signed. apply bv_swrap_small. change (bv_half_modulus 8) with 128. lia.
Qed.

(* A shadow value read through the view is a byte ctrl's mrd returns. *)
Lemma pwsh_view_mrd : forall (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) (s v : Z),
  lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m s = Some v ->
  exists b, lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 s) = Some b /\ bv_unsigned b = v.
Proof.
  intros W m s v Hv.
  destruct (lib.Reusable.YA0n.w_H W (Z_to_bv 64 s)) eqn:Hh.
  - exfalso. unfold lib.Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict in Hv.
    rewrite Hh in Hv. unfold lib.Reusable.YK11.seg_rom in Hv.
    rewrite (lib.Reusable.YK04.memory_read1_hidden segs _ (lib.Reusable.YA0n.w_Hoff W) _ Hh) in Hv.
    discriminate Hv.
  - rewrite (B.ProgWorld.aview_vis_mrd W m s Hh) in Hv.
    destruct (lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 s)) as [b|]; [|discriminate Hv].
    exists b. split; [reflexivity|]. injection Hv as Hv. exact Hv.
Qed.

(* The core's shadow address of a granule offset from an 8-aligned base is AsanRT's shadow address. *)
Lemma pwsh_shadow_eq : forall q a, q mod 8 = 0 ->
  lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF q + (a - q) / 8 = B.AsanRT.shadow_addr a.
Proof.
  intros q a Hq. rewrite <- (lib.Reusable.YG0v.shadow_of_addr_aligned_off _ q (a - q) Hq).
  replace (q + (a - q)) with a by lia.
  unfold lib.Reusable.YG0v.shadow_of_addr, B.AsanRT.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF, B.AsanRT.ASAN_K. lia.
Qed.

Lemma ctl_block_shadow_of_AR : B.ProgWorld.ctl_block_shadow_of_AR_stmt B.
Proof.
  intros ARL ly S W m md p n lo len HAR Hin Hlo Hlen Hhi.
  destruct (lib.Reusable.YG0d.al_blocks _ _ ARL ly S W m md p n HAR Hin) as (_ & H4096 & Hceil & Happ & _).
  destruct (lib.Reusable.YG0d.al_shadow _ _ ARL ly S W m md p n HAR Hin) as [Hbs _].
  destruct Hbs as (Hp8 & Hrs & Hsh).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_lt rc) as Hcl.
  unfold B.AsanRT.addressable. split; [lia|]. split; [exact Hlen|]. split.
  { unfold B.AsanRT.APPMEM_END. lia. }
  intros i Hi. unfold B.AsanRT.addr_byte. split.
  - unfold lib.Reusable.YG0f.in_app, lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg,
      lib.Reusable.YG0f.ASAN_CEIL in Happ.
    unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END.
    destruct Happ as (_ & [Hl | (Hh1 & Hh2)]); [left | right]; lia.
  - assert (Hj : 0 <= (lo + i - p) / 8 < (lib.Reusable.YG00.req_size n + 7) / 8) by lia.
    specialize (Hsh _ Hj). rewrite (pwsh_shadow_eq p (lo + i) Hp8) in Hsh.
    destruct (pwsh_view_mrd W m _ _ Hsh) as (b & Hb & Hbu).
    exists b. split; [exact Hb|].
    assert (Hsm : bv_unsigned b < 128).
    { rewrite Hbu. destruct (_ <? _); lia. }
    unfold B.AsanRT.shadow_ok. rewrite (pwsh_byte_signed_small b Hsm), Hbu.
    destruct (Z.ltb_spec ((lo + i - p) / 8) (lib.Reusable.YG00.req_size n / 8)) as [Hl | Hl].
    + left. reflexivity.
    + right. lia.
Qed.

Lemma ctl_zshadow_of_AR : B.ProgWorld.ctl_zshadow_of_AR_stmt B.
Proof.
  intros ARL ly S W m md r lo len HAR Hin Hlo Hlen Hhi.
  pose proof (lib.Reusable.YG0d.al_zshadow _ _ ARL ly S W m md r HAR) as Hz.
  specialize (Hz ltac:(unfold lib.Reusable.YG0n.zero_shadow_ranges; right; exact Hin)).
  assert (Hsyms : lib.Reusable.YG0f.asyms_ok B) by (destruct HAR as [HARm _]; destruct HARm; assumption).
  assert (Hzs : Forall (fun r => 0 <= fst r /\ 0 <= snd r /\ fst r mod 8 = 0 /\ snd r mod 8 = 0 /\
                                 fst r + snd r <= lib.Reusable.YG0f.kLowMemEnd) (lib.Reusable.YG0f.as_zero_shadow B))
    by (destruct Hsyms; assumption).
  rewrite Forall_forall in Hzs. destruct (Hzs r Hin) as (Hr0 & Hs0 & Hr8 & Hs8 & Hrlow).
  unfold lib.Reusable.YG0f.kLowMemEnd in Hrlow.
  unfold B.AsanRT.addressable. split; [lia|]. split; [exact Hlen|]. split.
  { unfold B.AsanRT.APPMEM_END. lia. }
  intros i Hi. unfold B.AsanRT.addr_byte. split.
  - unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END. left. lia.
  - assert (Hj : 0 <= (lo + i - fst r) / 8 < snd r / 8) by lia.
    specialize (Hz _ Hj). rewrite (pwsh_shadow_eq (fst r) (lo + i) Hr8) in Hz.
    destruct (pwsh_view_mrd W m _ _ Hz) as (b & Hb & Hbu).
    exists b. split; [exact Hb|].
    unfold B.AsanRT.shadow_ok. left. rewrite (pwsh_byte_signed_small b ltac:(lia)). exact Hbu.
Qed.

(* The stack window: zero_shadow_ranges' first entry (YG0n.v:188-189), page-aligned and in high memory by layout_ok's
   lo_top (YG0f.v:322-324). *)
Lemma ctl_stack_shadow_of_AR : B.ProgWorld.ctl_stack_shadow_of_AR_stmt B.
Proof.
  intros ARL ly S W m md lo len HAR Hlo Hlen Hhi.
  pose proof (lib.Reusable.YG0d.al_zshadow _ _ ARL ly S W m md
    (lib.Reusable.YG0f.ly_stk_lo ly, lib.Reusable.YG0f.ly_stk_hi ly - lib.Reusable.YG0f.ly_stk_lo ly) HAR) as Hz.
  specialize (Hz ltac:(unfold lib.Reusable.YG0n.zero_shadow_ranges; left; reflexivity)).
  assert (Hlay : lib.Reusable.YG0f.layout_ok ly) by (destruct HAR as [HARm _]; destruct HARm; assumption).
  assert (Htop : lib.Reusable.YG0f.ly_stk_lo ly <= lib.Reusable.YG0f.ly_bot ly /\
                 lib.Reusable.YG0f.ly_bot ly < lib.Reusable.YG0f.ly_top ly <= lib.Reusable.YG0f.ly_stk_hi ly /\
                 lib.Reusable.YG0f.page_aligned (lib.Reusable.YG0f.ly_top ly) /\
                 lib.Reusable.YG0f.ly_stk_hi ly <= lib.Reusable.YG0f.kHighMemEnd /\
                 lib.Reusable.YG0f.page_aligned (lib.Reusable.YG0f.ly_stk_lo ly) /\
                 lib.Reusable.YG0f.page_aligned (lib.Reusable.YG0f.ly_stk_hi ly) /\
                 lib.Reusable.YG0f.kHighMemBeg <= lib.Reusable.YG0f.ly_stk_lo ly)
    by (destruct Hlay; assumption).
  destruct Htop as (_ & _ & _ & Hend & Hal & Hah & Hbeg).
  unfold lib.Reusable.YG0f.page_aligned, lib.Reusable.YG0f.kHighMemEnd, lib.Reusable.YG0f.kHighMemBeg in *.
  assert (Hl8 : lib.Reusable.YG0f.ly_stk_lo ly mod 8 = 0) by lia.
  unfold B.AsanRT.addressable. split; [lia|]. split; [exact Hlen|]. split.
  { unfold B.AsanRT.APPMEM_END. lia. }
  intros i Hi. unfold B.AsanRT.addr_byte. split.
  - unfold B.AsanRT.app_mem, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END. right. lia.
  - assert (Hj : 0 <= (lo + i - lib.Reusable.YG0f.ly_stk_lo ly) / 8 <
                 (lib.Reusable.YG0f.ly_stk_hi ly - lib.Reusable.YG0f.ly_stk_lo ly) / 8) by lia.
    specialize (Hz _ Hj). cbn [fst snd] in Hz.
    rewrite (pwsh_shadow_eq (lib.Reusable.YG0f.ly_stk_lo ly) (lo + i) Hl8) in Hz.
    destruct (pwsh_view_mrd W m _ _ Hz) as (b & Hb & Hbu).
    exists b. split; [exact Hb|].
    unfold B.AsanRT.shadow_ok. left. rewrite (pwsh_byte_signed_small b ltac:(lia)). exact Hbu.
Qed.

(* ---- Global shadow: a Theorem Labs lane's ProgWorld statements ctl_gshadow_of_AR_stmt (AMENDED) and ctl_global_shadow_of_AR_stmt
   (B twins at lib/B/ProgWorld.v Section CtlBase3, of A's ProgWorld.v (from a working branch 1d23ced37fd), at head lib/A/ProgWorld.v:1116-1123
   / :1143-1154).  The a48c4068c6e text of ctl_gshadow_of_AR_stmt was FALSE (a Theorem Labs lane 05:47Z): image B's
   Tfib_const_abs holds the asan_inited row `z1 (ANum 0xaa398) 0x1` (B.AsanRT.INITED, lib/Reusable/YF0m.v:81), so
   g := 8 * (0xaa398 - 0x7fff8000) < 0 met every premise (shadow_addr g = 0xaa398, k = 1) while addressable needs
   0 <= g; the amended text adds the image bound kImgLo <= g, g + k <= kImgEnd (resp. g + n <= kImgEnd).  Sources:
   AR's am_const at as_const B ly = Tfib_const ly (CtrlTSyms' ts_const), the view -> mrd step pwsh_view_mrd,
   ctl_zshadow_of_AR for the full granules, am_static_img + lo_img for kImgLo <= fst r. ---- *)
Lemma ctl_gshadow_of_AR : B.ProgWorld.ctl_gshadow_of_AR_stmt B.
Proof.
  intros HTS _ ly S W m md g k lo len HAR Hin Hg8 Hglo Hghi Hk Hlo Hlen Hhi.
  destruct HAR as [HARm _].
  assert (Hc : Forall (lib.Reusable.YG0f.cell_holds B ly (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m))
                 (lib.Reusable.YG0f.as_const B ly)) by (destruct HARm; assumption).
  rewrite (lib.Reusable.YF0m.ts_const B HTS ly), Forall_forall in Hc.
  specialize (Hc _ Hin).
  unfold lib.Reusable.YG0f.cell_holds, lib.Reusable.YG0f.z1, lib.Reusable.YG0f.c1 in Hc.
  cbn [lib.Reusable.YG0f.c_at lib.Reusable.YG0f.c_w lib.Reusable.YG0f.c_val lib.Reusable.YG0f.aeval] in Hc.
  specialize (Hc 0%nat ltac:(lia)).
  assert (Hle : lib.Reusable.YG0f.le_byte k 1 0 = k).
  { unfold lib.Reusable.YG0f.le_byte. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
    change (2 ^ (8 * Z.of_nat 1)) with 256. rewrite Z.mod_mod by lia. apply Z.mod_small. lia. }
  rewrite Hle in Hc. change (Z.of_nat 0) with 0 in Hc. rewrite Z.add_0_r in Hc.
  destruct (pwsh_view_mrd W m _ _ Hc) as (b & Hb & Hbu).
  unfold lib.Reusable.YG0f.kImgLo, lib.Reusable.YG0f.kImgEnd in *.
  unfold B.AsanRT.addressable. split; [lia|]. split; [exact Hlen|]. split.
  { unfold B.AsanRT.APPMEM_END. lia. }
  intros i Hi. unfold B.AsanRT.addr_byte. split.
  - unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END. left. lia.
  - exists b. split.
    + assert (Hsa : B.AsanRT.shadow_addr (lo + i) = lib.Reusable.YG0f.shadow_addr g).
      { unfold B.AsanRT.shadow_addr, lib.Reusable.YG0f.shadow_addr, B.AsanRT.ASAN_K, lib.Reusable.YG0f.SHADOW_OFF. lia. }
      rewrite Hsa. exact Hb.
    + unfold B.AsanRT.shadow_ok. right. rewrite (pwsh_byte_signed_small b ltac:(lia)), Hbu. lia.
Qed.

Lemma pwsh_addressable_app : forall (m : word -> option byte) lo n1 n2,
  B.AsanRT.addressable m lo n1 -> B.AsanRT.addressable m (lo + n1) n2 -> B.AsanRT.addressable m lo (n1 + n2).
Proof.
  intros m lo n1 n2 (H0 & H1 & H2 & H3) (G0 & G1 & G2 & G3).
  unfold B.AsanRT.addressable. split; [exact H0|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (Z.lt_ge_cases i n1) as [Hl | Hl].
  - exact (H3 i ltac:(lia)).
  - replace (lo + i) with (lo + n1 + (i - n1)) by lia. exact (G3 (i - n1) ltac:(lia)).
Qed.

Lemma ctl_global_shadow_of_AR : B.ProgWorld.ctl_global_shadow_of_AR_stmt B.
Proof.
  intros HTS ARL ly S W m md g n r HAR Hg8 Hn Hin Hr Hfull Hrow Hend.
  pose proof (ctl_zshadow_of_AR ARL ly S W m md r g (8 * (n / 8)) HAR Hin Hr ltac:(lia) Hfull) as HZ.
  destruct (Z.eq_dec (n mod 8) 0) as [H0 | H0].
  - replace n with (8 * (n / 8)) by lia. exact HZ.
  - assert (Himg : lib.Reusable.YG0f.kImgLo <= fst r).
    { destruct HAR as [HARm _].
      assert (Hst : Forall (fun r0 => lib.Reusable.YG0f.zr_sub r0 (lib.Reusable.YG0f.ly_img ly))
                     (lib.Reusable.YG0f.as_owned_static B ++ lib.Reusable.YG0f.as_zero_shadow B))
        by (destruct HARm; assumption).
      assert (Hlay : lib.Reusable.YG0f.layout_ok ly) by (destruct HARm; assumption).
      assert (Hlo : fst (lib.Reusable.YG0f.ly_img ly) = lib.Reusable.YG0f.kImgLo /\ 0 < snd (lib.Reusable.YG0f.ly_img ly) /\
                    lib.Reusable.YG0f.kImgLo + snd (lib.Reusable.YG0f.ly_img ly) <= lib.Reusable.YG0f.kImgEnd /\
                    lib.Reusable.YG0f.page_aligned (snd (lib.Reusable.YG0f.ly_img ly)))
        by (destruct Hlay; assumption).
      rewrite Forall_forall in Hst. destruct (Hst r (in_or_app _ _ _ (or_intror Hin))) as [Z1 _].
      destruct Hlo as [L1 _]. lia. }
    pose proof (ctl_gshadow_of_AR HTS ARL ly S W m md (g + 8 * (n / 8)) (n mod 8) (g + 8 * (n / 8)) (n mod 8)
                  HAR (Hrow H0) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HP.
    replace n with (8 * (n / 8) + n mod 8) by lia.
    exact (pwsh_addressable_app m g _ _ HZ HP).
Qed.

(* ---- Const-row visibility: a Theorem Labs lane's ProgWorld statement ctl_const_vis_of_AR_stmt (a working branch
   e68ab922649, ProgWorld.v section ConstVis, item 19).  Route named there: the row holds over the view
   (ProgWorld_Fs.pw_row, AR's am_const at as_const B ly = Tfib_const ly), so the view reads byte a; a byte the view
   reads is visible (ProgWorldVisFrame.vis_of_aview, through w_Hoff); pw_z1_row gives the byte in bytes_at form. ---- *)
Lemma ctl_const_vis_of_AR : B.ProgWorld.ctl_const_vis_of_AR_stmt B.
Proof.
  intros TS ly S W m md e v a HAR Hin Ea Ha Hv. split.
  - pose proof (B.ProgWorld_Fs.pw_row B TS ly S W m md _ HAR Hin) as Hc.
    unfold lib.Reusable.YG0f.cell_holds in Hc.
    cbn [lib.Reusable.YG0f.c_at lib.Reusable.YG0f.c_val lib.Reusable.YG0f.c_w lib.Reusable.YG0f.z1
         lib.Reusable.YG0f.c1 lib.Reusable.YG0f.aeval] in Hc.
    specialize (Hc 0%nat ltac:(lia)). rewrite Ea in Hc. replace (a + Z.of_nat 0) with a in Hc by lia.
    apply (B.ProgWorldVisFrame.vis_of_aview segs W m a). rewrite Hc. discriminate.
  - exact (B.ProgWorld_Fs.pw_z1_row B TS ly S W m md e a v HAR Hin Ea Ha Hv).
Qed.

End Shadow.
