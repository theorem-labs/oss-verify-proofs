(* pcap_source_next (fuzz_pcap.asan 0x8181c) on libreac v1.9.0's ASan build: the phase from the head
   of the record loop NP_loop (0x81998) to the return of the fread of the 16-byte record header,
   NP_hd_ra (0x819bc).

   Every number is read from the pinned fuzz_pcap.asan image
   (sha256 b7a91d9b1fb0017d...; capstone 5 disassembly of 0x81998..0x819bc and of the error path
   0x81e68):
     0x81998 sb zero,4(s3)     0x8199c sb zero,5(s3)    the header `ph` (F+32..F+47) in scope
     0x819a0 lbu a0,0(s8)      0x819a4 bnez a0,0x81e68  the shadow check of ps (8-byte load)
     0x819a8 ld a3,0(s5)                                a3 := ps->f = h
     0x819ac addi a1,zero,1    0x819b0 addi a2,zero,16  0x819b4 mv a0,s10 (= F + 32)
     0x819b8 jal __interceptor_trampoline_fread         fread(F + 32, 1, 16, h), returns to 0x819bc
   The branch at 0x819a4 goes to 0x81e68 (`mv a0,s5; jal __asan_report_load8`), the error path. It is
   not taken: the shadow byte of ps is 0, because the caller's ps is addressable for 8 bytes (an
   8-aligned granule whose last byte is addressable has shadow 0, YG0v.saddr_ok); the walk proves
   this from the premise, no stack constant budgets that path.

   The fread is the wrapper's contract afread_spec (lib/A/Stdio/PFreadISpec.v, the caller-journal
   form) at the site whose return address is NP_hd_ra. Its destination is the header `ph`, 16 bytes
   of THIS call's own class-0 frame (rread_at's frame arm); the right to write it is awr_byte's
   frame case (the frame is the head of the journal's `own`), the right to write the FILE block
   comes from the statement's premise on asource_fp through awr_byte's footprint and tmp-block
   cases. The post extends the caller's journal directly, so no composition lemma is needed.

   THE WALK. hd_to_call runs 0x81998 .. 0x819b8 on a phase-local symbolic state (hd_ss: the frame's
   two shadow bytes, the shadow byte of ps, ps->f); hd_land rebuilds PcapSourceNextHdrBDefs.v's nx_hdra_inv from the
   loop head's invariant, the run's state at the call and the fread's post; pb_hdA is the phase
   lemma in the shape PcapSourceNext.v takes (H_hdA). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 PcapImgEnd YC5d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym PaShadow.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal PcapSyms PcapList PcapAddr PcapPa PcapPaLib PcapBase YC1g YC4b YC85 YC45 PcapFrame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PFreadM PFreadISpec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSourceNextDefs PcapSourceNextHdrBDefs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSourceNextKit.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSourceMeta.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require PcapSourceClose.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the header `ph` and its two shadow bytes ---- *)

(* The frame's class: 64 bytes, 8 shadow bytes (NX_FRAME_slot). *)
Lemma hd_fsb : fs_frame_bytes NX_CID = 64.
Proof. vm_compute. reflexivity. Qed.

(* With the shadow bytes 4 and 5 of an 8-aligned frame F at 0 (0x81998, 0x8199c), the 16 bytes
   F + 32 .. F + 47 are addressable: they are the granules 4 and 5. *)
Lemma hd_ph_ra : forall (rd : Z -> option Z) F, F mod 8 = 0 ->
  rd (shadow_of_addr SHADOW_OFF F + 4) = Some 0 -> rd (shadow_of_addr SHADOW_OFF F + 5) = Some 0 ->
  range_addressable rd SHADOW_OFF (F + NO_PH) NX_PH_LEN.
Proof.
intros rd F HF H4 H5 x Hx. unfold NO_PH, NX_PH_LEN in Hx. exists 0. split; [|left; reflexivity].
replace x with (F + (x - F)) by lia. rewrite shadow_of_addr_aligned_off by exact HF.
destruct (Z_lt_dec x (F + 40)) as [Hl|Hl].
- assert (Hq : (x - F) / 8 = 4) by (symmetry; apply Z.div_unique with (r := x - F - 32); lia).
  rewrite Hq. exact H4.
- assert (Hq : (x - F) / 8 = 5) by (symmetry; apply Z.div_unique with (r := x - F - 40); lia).
  rewrite Hq. exact H5.
Qed.

(* ---- the symbolic state of the run 0x81998 .. 0x819b8 ---- *)

(* The run's atoms are the registers at NP_loop (Eimg (Ereg regs [h]): atom r is x_r, atom 32 is
   the stream h = ps->f). It touches three places, one region each:
   - the frame's shadow bytes 4 and 5, at s3 + 4 (x19 = the frame's shadow address), written;
   - the shadow byte of ps, at s8 (x24 = the shadow address of ps), read: it is 0;
   - ps->f, the 8 bytes at s5 (x21 = ps), read: it is h. *)
Definition hd_regions : YP09.smem :=
  [ YP09.mkRegion (Some 19%nat) 4 6 4 6 [];
    YP09.mkRegion (Some 24%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))];
    YP09.mkRegion (Some 21%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))] ].
Definition hd_ss : sstate := mkSS NP_loop sr_atoms hd_regions None (mkFacts [] [] []).

(* The shadow of an address below 2^47 lies in [SHADOW_OFF, kHighMemBeg), away from application
   memory (amem_range). *)
Lemma hd_shadow_apart : forall x y n m, 0 <= x -> 0 <= m -> x + 8 * m <= 2 ^ 47 -> amem_range y n -> 0 <= n ->
  y + n <= shadow_of_addr SHADOW_OFF x \/ shadow_of_addr SHADOW_OFF x + m <= y.
Proof.
intros x y n m Hx0 Hm Hx Hy Hn.
assert (x / 8 <= 2 ^ 44 - m) by (apply Z.div_le_upper_bound; lia).
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
unfold amem_range, shadow_of_addr, SHADOW_OFF, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg pcap_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
#[local] Notation SIGMA := (pa_sigma).
#[local] Notation BASE := (pa_val A_TEXT).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable KS : asource_syms.
Hypothesis LAWS : AR_laws SEGS B.

Lemma hd_awr : forall E STK sp0 FP bl0 blc ly fp own,
  bv_unsigned (ew E 19%nat) = shadow_addr (frame_addr ly NX_CID fp) ->
  awr_ok E hd_regions STK sp0 FP bl0 blc ly ((NX_CID, fp) :: own).
Proof.
intros E STK sp0 FP bl0 blc ly fp own H19. unfold hd_regions.
eapply awr_ok_cons_gen; [reflexivity | exact H19 | |].
- intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. apply awr_byte_own_head_shadow.
  rewrite hd_fsb. change (64 / 8) with 8. lia.
- apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil.
Qed.

(* The symbolic state at NP_loop, from the machine state's facts. *)
Lemma hd_st0 : forall (W3 : world SEGS) (ms3 : machine_state) (h F ps : Z),
  ms_pc_val ms3 = w64 (BASE + NP_loop) -> ms_resv ms3 = None -> ms_svc_pending ms3 = None ->
  ms_rom ms3 = seg_rom SEGS -> ms_fregs ms3 = fp_regs -> ms_fcsr ms3 = fp_csr ->
  getr (ms_regs ms3) 19 = w64 (shadow_of_addr SHADOW_OFF F) ->
  getr (ms_regs ms3) 24 = w64 (shadow_of_addr SHADOW_OFF ps) ->
  getr (ms_regs ms3) 21 = w64 ps ->
  0 <= h < 2 ^ 64 -> F mod 8 = 0 -> 0 <= F -> F + 64 <= 2 ^ 47 ->
  ps mod 8 = 0 -> 0 <= ps /\ ps + 8 <= 2 ^ 47 -> amem_range ps 8 -> (ps + 8 <= F \/ F + 64 <= ps) ->
  apresent (w_H W3) (ms_mem ms3) (shadow_of_addr SHADOW_OFF F + 4) ->
  apresent (w_H W3) (ms_mem ms3) (shadow_of_addr SHADOW_OFF F + 5) ->
  aview SEGS (w_H W3) (ms_mem ms3) (shadow_of_addr SHADOW_OFF ps) = Some 0 ->
  val_mem SEGS (rdW W3 (ms_mem ms3)) ps 8 h ->
  st_ok_pi SEGS VAL (Eimg (Ereg (ms_regs ms3) [w64 h])) hd_ss (restrict (w_H W3) ms3).
Proof.
intros W3 ms3 h F ps Hpc Hresv Hpend Hrom Hfr Hfc R19 R24 R21 Hh HF8 HF0 HF47 Hps8 Hps Hpsr Hdisj
  Hp4 Hp5 Hsh Hv.
assert (Hms : restrict (w_H W3) ms3 =
              mkst (ms_regs ms3) (Z_to_bv 64 (BASE + NP_loop)) (mrestrict (w_H W3) (ms_mem ms3))
                   (seg_rom SEGS)).
{ destruct ms3 as [regs0 fregs0 pcv0 pend0 resv0 fcsr0 mem0 rom0].
  cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem]
    in Hpc, Hresv, Hpend, Hrom, Hfr, Hfc.
  subst. reflexivity. }
set (E := Eimg (Ereg (ms_regs ms3) [w64 h])).
assert (E19 : ew E 19 = getr (ms_regs ms3) 19) by exact (ew_Eimg_Ereg_nat (ms_regs ms3) _ 19 19%bv eq_refl).
assert (E24 : ew E 24 = getr (ms_regs ms3) 24) by exact (ew_Eimg_Ereg_nat (ms_regs ms3) _ 24 24%bv eq_refl).
assert (E21 : ew E 21 = getr (ms_regs ms3) 21) by exact (ew_Eimg_Ereg_nat (ms_regs ms3) _ 21 21%bv eq_refl).
assert (E32 : ew E 32 = w64 h)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms3) _ 0)).
assert (HF8' : F / 8 < 2 ^ 44 - 7) by (apply Z.div_lt_upper_bound; lia).
pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)) as HF8p.
assert (Hps8' : ps / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
pose proof (Z.div_pos ps 8 ltac:(lia) ltac:(lia)) as Hps8p.
assert (B19 : bv_unsigned (ew E 19) = shadow_of_addr SHADOW_OFF F).
{ rewrite E19, R19. unfold w64. apply unsigned_lit_small. unfold shadow_of_addr, SHADOW_OFF. lia. }
assert (B24 : bv_unsigned (ew E 24) = shadow_of_addr SHADOW_OFF ps).
{ rewrite E24, R24. unfold w64. apply unsigned_lit_small. unfold shadow_of_addr, SHADOW_OFF. lia. }
assert (B21 : bv_unsigned (ew E 21) = ps) by (rewrite E21, R21; unfold w64; apply unsigned_lit_small; lia).
(* the shadow of ps and the frame's shadow bytes 4, 5 are apart: ps is not in the frame *)
assert (Dsh : shadow_of_addr SHADOW_OFF ps + 1 <= shadow_of_addr SHADOW_OFF F + 4 \/
              shadow_of_addr SHADOW_OFF F + 6 <= shadow_of_addr SHADOW_OFF ps).
{ pose proof (Z.div_mod ps 8 ltac:(lia)) as Dp. pose proof (Z.div_mod F 8 ltac:(lia)) as DF.
  rewrite Hps8, Z.add_0_r in Dp. rewrite HF8, Z.add_0_r in DF. unfold shadow_of_addr. lia. }
pose proof (hd_shadow_apart F ps 8 8 HF0 ltac:(lia) ltac:(lia) Hpsr ltac:(lia)) as DFp.
pose proof (hd_shadow_apart ps ps 8 1 ltac:(lia) ltac:(lia) ltac:(lia) Hpsr ltac:(lia)) as Dpp.
assert (Vsh : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms3)) (shadow_of_addr SHADOW_OFF ps + 0) 1 0).
{ intros k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite !Z.add_0_r. unfold aview in Hsh.
  destruct (mbyte SEGS (mrestrict (w_H W3) (ms_mem ms3)) (shadow_of_addr SHADOW_OFF ps)) as [b0|] eqn:Hb;
    [|discriminate Hsh].
  cbn [option_map] in Hsh. injection Hsh as Hsh. f_equal. apply bv_eq. rewrite Hsh. vm_compute. reflexivity. }
assert (RF : 0 <= shadow_of_addr SHADOW_OFF F /\ shadow_of_addr SHADOW_OFF F + 8 <= 2 ^ 64)
  by (unfold shadow_of_addr, SHADOW_OFF; lia).
assert (Rp : 0 <= shadow_of_addr SHADOW_OFF ps /\ shadow_of_addr SHADOW_OFF ps + 8 <= 2 ^ 64)
  by (unfold shadow_of_addr, SHADOW_OFF; lia).
rewrite Hms. unfold hd_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold hd_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite B19. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS).
    assert (o = 4 \/ o = 5) as [-> | ->] by lia; [exact Hp4 | exact Hp5].
  + rewrite B24. split; [lia|]. split; [lia|].
    split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ _ 0 1%N (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | exact Vsh].
  + rewrite B21. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ _ 0 8%N (SOff 32 0) h); [| cbn; lia | cbn; lia |].
    * cbn [sv_denot]. rewrite E32, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity.
    * rewrite Z.add_0_r. exact Hv.
- apply pairwise_disjoint_of_extents. unfold hd_regions, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite B19, B24, B21.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; lia.
- unfold facts_ok. cbn. repeat split.
Qed.

Let RUNP := SRr_run_pi_AJ (PL := PL_pcap) B LAWS.
Let RUNC := SRr_run_pi_AJ_call (PL := PL_pcap) B LAWS.

(* THE RUN 0x81998 .. 0x819b8, up to the entry of the fread wrapper: the two shadow stores, the
   shadow check of ps and its branch to the error path 0x81e68 (NOT taken: the shadow byte is the
   region's chunk 0, so the engine resolves `bnez` statically), ps->f, the arguments and the `jal`.
   The machine state at the wrapper's entry: the registers but a0..a3 and ra as at NP_loop, the
   memory but the frame's shadow bytes 4 and 5 (now 0) as at NP_loop, the same journal. *)
Lemma hd_to_call : forall (W3 : world SEGS) (ms3 : machine_state) md3 (h F ps : Z)
  STK sp0 FP ly S W0 mem0 md0 own ly3 S3 k2 fp (Q : world SEGS -> config -> Prop),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 ((NX_CID, fp) :: own) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  shadow_addr (frame_addr ly3 NX_CID fp) = shadow_of_addr SHADOW_OFF F ->
  ms_pc_val ms3 = w64 (BASE + NP_loop) -> ms_resv ms3 = None -> ms_svc_pending ms3 = None ->
  ms_rom ms3 = seg_rom SEGS -> ms_fregs ms3 = fp_regs -> ms_fcsr ms3 = fp_csr ->
  getr (ms_regs ms3) 19 = w64 (shadow_of_addr SHADOW_OFF F) ->
  getr (ms_regs ms3) 24 = w64 (shadow_of_addr SHADOW_OFF ps) ->
  getr (ms_regs ms3) 21 = w64 ps ->
  0 <= h < 2 ^ 64 -> F mod 8 = 0 -> 0 <= F -> F + 64 <= 2 ^ 47 ->
  ps mod 8 = 0 -> 0 <= ps /\ ps + 8 <= 2 ^ 47 -> amem_range ps 8 -> (ps + 8 <= F \/ F + 64 <= ps) ->
  apresent (w_H W3) (ms_mem ms3) (shadow_of_addr SHADOW_OFF F + 4) ->
  apresent (w_H W3) (ms_mem ms3) (shadow_of_addr SHADOW_OFF F + 5) ->
  aview SEGS (w_H W3) (ms_mem ms3) (shadow_of_addr SHADOW_OFF ps) = Some 0 ->
  val_mem SEGS (rdW W3 (ms_mem ms3)) ps 8 h ->
  (forall (regsc : bvmap 5 word) memc mdc,
     ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 ((NX_CID, fp) :: own) ly3 S3 W3 memc mdc k2 ->
     aregs_preserved (ms_regs ms3) regsc ->
     getr regsc 1 = Z_to_bv 64 (BASE + NP_hd_ra) ->
     getr regsc 10 = getr (ms_regs ms3) 26 ->
     getr regsc 11 = w64 1 -> getr regsc 12 = w64 16 -> getr regsc 13 = w64 h ->
     (forall a, 0 <= a < 2 ^ 64 -> a <> shadow_of_addr SHADOW_OFF F + 4 -> a <> shadow_of_addr SHADOW_OFF F + 5 ->
        aview SEGS (w_H W3) memc a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
     aview SEGS (w_H W3) memc (shadow_of_addr SHADOW_OFF F + 4) = Some 0 ->
     aview SEGS (w_H W3) memc (shadow_of_addr SHADOW_OFF F + 5) = Some 0 ->
     m_fds mdc = m_fds md3 -> m_fs mdc = m_fs md3 ->
     SRr SEGS W3 (mkCfg (mkst regsc (Z_to_bv 64 (SIGMA PS___interceptor_trampoline_fread)) memc
       (seg_rom SEGS)) mdc) Q) ->
  SRr SEGS W3 (mkCfg ms3 md3) Q.
Proof.
intros W3 ms3 md3 h F ps STK sp0 FP ly S W0 mem0 md0 own ly3 S3 k2 fp Q HJ HSA Hpc Hresv Hpend Hrom
  Hfr Hfc R19 R24 R21 Hh HF8 HF0 HF47 Hps8 Hps Hpsr Hdisj Hp4 Hp5 Hsh Hv HK.
pose proof (hd_st0 W3 ms3 h F ps Hpc Hresv Hpend Hrom Hfr Hfc R19 R24 R21 Hh HF8 HF0 HF47 Hps8 Hps Hpsr
  Hdisj Hp4 Hp5 Hsh Hv) as HS.
set (E := Eimg (Ereg (ms_regs ms3) [w64 h])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg (ms_regs ms3) [w64 h]) E)
  by (split; [intros n Hn; subst E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E19 : ew E 19 = getr (ms_regs ms3) 19) by exact (ew_Eimg_Ereg_nat (ms_regs ms3) _ 19 19%bv eq_refl).
assert (E26 : ew E 26 = getr (ms_regs ms3) 26) by exact (ew_Eimg_Ereg_nat (ms_regs ms3) _ 26 26%bv eq_refl).
assert (E32 : ew E 32 = w64 h)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms3) _ 0)).
assert (HF8' : F / 8 < 2 ^ 44 - 7) by (apply Z.div_lt_upper_bound; lia).
pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)) as HF8p.
assert (B19 : bv_unsigned (ew E 19) = shadow_of_addr SHADOW_OFF F).
{ rewrite E19, R19. unfold w64. apply unsigned_lit_small. unfold shadow_of_addr, SHADOW_OFF. lia. }
paj_run_shc RUNP RUNC HS HJ.
- apply hd_awr. rewrite B19. exact (eq_sym HSA).
- lazymatch type of HS with st_ok _ _ ?ssx (restrict _ ?msx) =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
    pose proof (st_ok_region_nth E ssx (restrict (w_H W3) msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
    cbn [ms_mem restrict] in HR0 end.
  assert (V4 : forall od, In (YP09.mkChunk od (CVal 1 (SLit 0))) [YP09.mkChunk 5 (CVal 1 (SLit 0)); YP09.mkChunk 4 (CVal 1 (SLit 0))] ->
    aview SEGS (w_H W3) (ms_mem ms) (shadow_of_addr SHADOW_OFF F + od) = Some 0).
  { intros od Hod. apply (aview_of_val_mem1 SEGS); [|lia].
    exact (field_of_region E _ 19 (shadow_of_addr SHADOW_OFF F) _ 4 6 4 6 od 1%N (SLit 0) 0 HR0 B19 Hod
             eq_refl ltac:(cbn; lia) ltac:(cbn; lia)). }
  pmkst HS.
  apply HK.
  + exact HJ.
  + eapply aregs_preserved_of_st_ok; [exact HS | exact HAE | vm_compute; reflexivity].
  + prreg HS (1%bv : bv 5) Q1. rewrite Q1. first [reflexivity | exact (codeptr_val E NP_hd_ra HEI)].
  + prreg HS (10%bv : bv 5) Q10. rewrite Q10. first [exact E26 | reflexivity | subst E; exact E26].
  + prreg HS (11%bv : bv 5) Q11. rewrite Q11. reflexivity.
  + prreg HS (12%bv : bv 5) Q12. rewrite Q12. reflexivity.
  + prreg HS (13%bv : bv 5) Q13. rewrite Q13. first [exact E32 | reflexivity | subst E; exact E32].
  + intros a Ha H4 H5.
    apply (aview_kept_out E hd_regions (w_H W3) (ms_mem ms3) (ms_mem ms)); [exact HFr | exact Ha|].
    intros (r & Hin & Har). unfold hd_regions in Hin. cbn [In] in Hin.
    destruct Hin as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Har;
      [rewrite B19 in Har | lia | lia]. lia.
  + apply V4. right. left. reflexivity.
  + apply V4. left. reflexivity.
  + reflexivity.
  + reflexivity.
Qed.

(* A live block and the header are apart (AR_sep_law: a block and a frame are disjoint). *)
Lemma hd_ph_blk : forall ly S W mem md fp p n,
  AR SEGS B ly S W mem md -> In (NX_CID, fp) (frames S) -> In (p, n) (ablocks B ly S) ->
  frame_addr ly NX_CID fp + NO_PH + NX_PH_LEN <= p \/ p + n <= frame_addr ly NX_CID fp + NO_PH.
Proof.
intros ly S W mem md fp p n HAR Hin Hb.
pose proof (sep_block_frame SEGS B LAWS ly S W mem md p n NX_CID fp HAR Hb Hin) as D.
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hb) as (_ & _ & _ & _ & _ & _ & Hn).
pose proof (req_size_pos n ltac:(lia)) as [_ Hq].
unfold zdisjoint in D. cbn [fst snd] in D. rewrite hd_fsb in D. unfold NO_PH, NX_PH_LEN. lia.
Qed.

(* The header's place: in application memory, under the heap ceiling. *)
Lemma hd_ph_place : forall ly S W mem md fp,
  AR SEGS B ly S W mem md -> In (NX_CID, fp) (frames S) ->
  4096 <= frame_addr ly NX_CID fp /\ frame_addr ly NX_CID fp + 64 <= alloc_ceiling /\
  frame_addr ly NX_CID fp mod 64 = 0 /\
  amem_range (frame_addr ly NX_CID fp + NO_PH) NX_PH_LEN.
Proof.
intros ly S W mem md fp HAR Hin.
destruct (frames_bounds SEGS B LAWS ly S W mem md NX_CID fp HAR Hin) as (H4096 & Hceil & _).
pose proof (frame_al64 SEGS B ly S W mem md NX_CID fp HAR Hin) as (H64 & _ & _).
rewrite hd_fsb in Hceil. pose proof asan_consts as (C1 & _).
split; [exact H4096|]. split; [exact Hceil|]. split; [exact H64|].
unfold amem_range, NO_PH, NX_PH_LEN, kHighMemBeg, kHighMemEnd, kLowMemEnd.
destruct (Z_lt_dec (frame_addr ly NX_CID fp + 48) 0x7fff8000); [left; lia|].
right. split; [|lia].
(* a frame is in application memory: in_app *)
destruct (frames_bounds SEGS B LAWS ly S W mem md NX_CID fp HAR Hin) as (_ & _ & Happ).
unfold in_app, kLowShadowBeg, kHighMemBeg in Happ. rewrite hd_fsb in Happ. lia.
Qed.

(* ---- the phase's geometry: nx_base and the journal at NP_loop ---- *)

(* The shadow ranges of two disjoint 8-aligned ranges are disjoint. *)
Lemma hd_shadow_disj : forall x n y m, x mod 8 = 0 -> n mod 8 = 0 -> y mod 8 = 0 -> m mod 8 = 0 ->
  0 <= x -> 0 <= y -> 0 <= n -> 0 <= m -> (x + n <= y \/ y + m <= x) ->
  shadow_addr x + n / 8 <= shadow_addr y \/ shadow_addr y + m / 8 <= shadow_addr x.
Proof.
intros x n y m Hx Hn Hy Hm Hx0 Hy0 Hn0 Hm0 D.
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.div_mod n 8 ltac:(lia)) as Dn.
pose proof (Z.div_mod y 8 ltac:(lia)) as Dy. pose proof (Z.div_mod m 8 ltac:(lia)) as Dm.
rewrite Hx, Z.add_0_r in Dx. rewrite Hn, Z.add_0_r in Dn. rewrite Hy, Z.add_0_r in Dy. rewrite Hm, Z.add_0_r in Dm.
unfold shadow_addr. lia.
Qed.

Section d.
Variables (cx : ncx) (fp k2 : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (ms3 : machine_state) (md3 : Model).
Hypothesis HB : nx_base SK B KS cx.
Hypothesis HJ : ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
  ((NX_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2.
Hypothesis HFR : frames S3 = (NX_CID, fp) :: frames (n_Sc cx).
Hypothesis HAB : ablocks B ly3 S3 = ablocks B (n_lyc cx) (n_Sc cx).

Lemma hd_fin : In (NX_CID, fp) (frames S3).
Proof. rewrite HFR. left. reflexivity. Qed.
Lemma hd_fin_c : forall c p, In (c, p) (frames (n_Sc cx)) -> In (c, p) (frames S3).
Proof. intros c p H. rewrite HFR. right. exact H. Qed.
Lemma hd_AR : AR SEGS B ly3 S3 W3 (ms_mem ms3) md3.
Proof. exact (proj1 HJ). Qed.
Lemma hd_fa : forall c p, frame_addr ly3 c p = frame_addr (n_lyc cx) c p.
Proof.
intros c p. pose proof HB as (HJ0 & _). pose proof HJ0 as (_ & Hly0 & _). pose proof HJ as (_ & Hly & _).
rewrite (frame_addr_layout_le _ _ _ Hly), (frame_addr_layout_le _ _ _ Hly0). reflexivity.
Qed.
Lemma hd_top : ly_top ly3 = ly_top (n_lyc cx).
Proof.
pose proof HB as (HJ0 & _). pose proof HJ0 as (_ & Hly0 & _). pose proof HJ as (_ & Hly & _).
pose proof Hly0 as (_ & _ & _ & _ & _ & _ & _ & _ & E0 & _). pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & E1 & _).
rewrite E1, E0. reflexivity.
Qed.
Lemma hd_cframes : forall c p, In (c, p) (n_own cx) -> In (c, p) (frames (n_Sc cx)).
Proof.
intros c p H. pose proof HB as (HJ0 & _). pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs & _).
rewrite Hfrs. apply in_or_app. left. exact H.
Qed.

(* This call's frame F = nF cx fp: 64 bytes in application memory, 64-aligned, under the heap ceiling. *)
Lemma hd_Ff : 4096 <= nF cx fp /\ nF cx fp + 64 <= alloc_ceiling /\ nF cx fp mod 64 = 0 /\ in_app (nF cx fp) 64.
Proof.
unfold nF. rewrite <- hd_fa.
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 NX_CID fp hd_AR hd_fin) as (H1 & H2 & H3).
pose proof (frame_al64 SEGS B ly3 S3 W3 (ms_mem ms3) md3 NX_CID fp hd_AR hd_fin) as (H64 & _).
rewrite hd_fsb in H2, H3. tauto.
Qed.
Lemma hd_SH : nSH cx fp = shadow_addr (frame_addr ly3 NX_CID fp).
Proof. unfold nSH, shadow_of_addr, shadow_addr, nF. rewrite hd_fa. reflexivity. Qed.

(* The stack: the caller's window lies above the heap ceiling; the realigned s1 is 224 .. 240 below
   the entry sp, 32-aligned. *)
Lemma hd_spf : alloc_ceiling + NX_STK <= spZ (n_regs cx) /\ spZ (n_regs cx) <= 2 ^ 47 /\
  spZ (n_regs cx) mod 16 = 0 /\
  spZ (n_regs cx) - 240 <= n_sp1 cx <= spZ (n_regs cx) - 224 /\ n_sp1 cx mod 32 = 0.
Proof.
pose proof HB as (HJ0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hal16 & Hwin & Hspsp0 & _).
pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _). pose proof asan_consts as (C1 & _).
assert (Hs : 0 <= spZ (n_regs cx) - NX_MFRAME) by (unfold NX_STK, AFREAD_STK, NX_MFRAME in *; lia).
assert (Hm : (spZ (n_regs cx) - NX_MFRAME) mod 16 = 0)
  by (unfold NX_MFRAME; rewrite <- Zminus_mod_idemp_l, Hal16; reflexivity).
pose proof (sp1_facts _ Hs Hm) as (Hb & Hal32 & _).
unfold n_sp1, nx_sp1. unfold NX_STK, AFREAD_STK, NX_MFRAME in *. lia.
Qed.

(* A frame of the caller and this call's frame are apart (AR_sep_law over frames S3). *)
Lemma hd_sep_cf : forall c p, In (c, p) (frames (n_Sc cx)) ->
  nF cx fp + 64 <= frame_addr (n_lyc cx) c p \/ frame_addr (n_lyc cx) c p + fs_frame_bytes c <= nF cx fp.
Proof.
intros c p Hin. destruct (in_split _ _ Hin) as (l2 & l3 & El).
pose proof (sep_frames_pos SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 (NX_CID, fp) (c, p) [] l2 l3 hd_AR
  ltac:(rewrite HFR, El; reflexivity)) as D.
unfold zdisjoint, frame_rng in D. cbn [fst snd] in D. rewrite !hd_fa, hd_fsb in D. unfold nF. lia.
Qed.
(* ... and so are their shadows. *)
Lemma hd_sep_cfs : forall c p, In (c, p) (frames (n_Sc cx)) ->
  nSH cx fp + 8 <= shadow_addr (frame_addr (n_lyc cx) c p) \/
  shadow_addr (frame_addr (n_lyc cx) c p) + fs_frame_bytes c / 8 <= nSH cx fp.
Proof.
intros c p Hin. pose proof (hd_fin_c c p Hin) as Hin3.
pose proof (frame_al64 SEGS B ly3 S3 W3 (ms_mem ms3) md3 c p hd_AR Hin3) as (Ha & Hb & H64).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 c p hd_AR Hin3) as (H1 & _).
rewrite hd_fa in Ha, H1. pose proof hd_Ff as (HF1 & _ & HF64 & _).
pose proof (hd_shadow_disj (nF cx fp) 64 (frame_addr (n_lyc cx) c p) (fs_frame_bytes c)) as D.
assert (M8 : forall z, z mod 64 = 0 -> z mod 8 = 0).
{ intros z Hz. apply Z.mod_divide in Hz; [|lia]. apply Z.mod_divide; [lia|]. destruct Hz as [q Hq]. exists (8 * q). lia. }
rewrite hd_SH. unfold nF in *. rewrite hd_fa.
change (64 / 8) with 8 in D. pose proof (hd_sep_cf c p Hin) as Dcf. unfold nF in Dcf.
apply D. all: try exact Dcf. all: try (apply M8; assumption). all: try reflexivity. all: lia.
Qed.

Lemma hd_SHr : SHADOW_OFF + 512 <= nSH cx fp /\ nSH cx fp + 8 <= kHighMemBeg.
Proof.
pose proof hd_Ff as (HF1 & HF2 & _). pose proof asan_consts as (C1 & _).
assert (512 <= nF cx fp / 8) by (apply Z.div_le_lower_bound; lia).
assert (nF cx fp / 8 + 8 <= 2 ^ 44) by (assert (nF cx fp / 8 <= 2 ^ 44 - 8) by (apply Z.div_le_upper_bound; lia); lia).
unfold nSH, shadow_of_addr, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.

(* The FILE block of an open reader: a live block of the caller, apart from this call's frame. *)
Lemma hd_hblk : n_h cx <> 0 ->
  In (n_h cx, SRC_FILE_BLOCK) (ablocks B ly3 S3) /\ 4096 <= n_h cx /\
  n_h cx + SRC_FILE_BLOCK <= alloc_ceiling /\ in_app (n_h cx) SRC_FILE_BLOCK /\
  (nF cx fp + 64 <= n_h cx \/ n_h cx + SRC_FILE_BLOCK <= nF cx fp).
Proof.
intros Hh. pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstr & _).
destruct (Hstr Hh) as (Hin & _). rewrite <- HAB in Hin.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ hd_AR Hin) as (_ & H4096 & Hceil & Happ & _).
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 _ _ NX_CID fp hd_AR Hin hd_fin) as D.
unfold zdisjoint in D. cbn [fst snd] in D. rewrite hd_fa, hd_fsb in D.
change (req_size SRC_FILE_BLOCK) with 1304 in *. unfold SRC_FILE_BLOCK. unfold nF. tauto.
Qed.

(* ---- what the run and the fread keep ---- *)
Section f.
Variables (memc : word -> option byte) (W4 : world SEGS) (mem4 : word -> option byte).
Hypothesis Hh : n_h cx <> 0.
Hypothesis HRUN : forall a, 0 <= a < 2 ^ 64 -> a <> nSH cx fp + 4 -> a <> nSH cx fp + 5 ->
  aview SEGS (w_H W3) memc a = aview SEGS (w_H W3) (ms_mem ms3) a.
Hypothesis HK4 : rread_kept SEGS B AFREAD_STK ly3 S3 W3 memc W4 mem4 (n_sp1 cx)
  (rread_wrset (n_h cx) (nF cx fp + NO_PH) NX_PH_LEN).

Local Ltac geo := pose proof hd_Ff as (HF1 & HF2 & HF64 & HFapp); pose proof hd_SHr as (HS1 & HS2);
  pose proof (hd_hblk Hh) as (Hhin & Hh1 & Hh2 & Hhapp & Hhd); pose proof hd_spf as (Hsp1 & Hsp2 & Hsp3 & Hsp4 & Hsp5);
  pose proof asan_consts as (C1 & _); unfold in_app, kLowShadowBeg, kHighMemBeg, SRC_FILE_BLOCK,
  NX_STK, AFREAD_STK, NO_PH, NX_PH_LEN, SHADOW_OFF, ASAN_CEIL in *.

Lemma hd_keep_stack : forall a, n_sp1 cx <= a < 2 ^ 64 ->
  aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) (ms_mem ms3) a.
Proof.
intros a Ha. pose proof HK4 as (K1 & _). geo.
rewrite (K1 a); [| lia | lia | unfold rread_wrset, SRC_FILE_BLOCK; intros [H|H]; lia].
apply HRUN; lia.
Qed.

Lemma hd_keep_frame : forall a, nF cx fp <= a < nF cx fp + 64 ->
  ~ (nF cx fp + NO_PH <= a < nF cx fp + NO_PH + NX_PH_LEN) ->
  aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) (ms_mem ms3) a.
Proof.
intros a Ha Hn. pose proof HK4 as (_ & _ & _ & K4 & _). geo.
rewrite (K4 NX_CID fp a hd_fin).
- apply HRUN; lia.
- left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite hd_fa, hd_fsb. unfold nF in *. lia.
- unfold rread_wrset, SRC_FILE_BLOCK. intros [H|H]; lia.
Qed.

Lemma hd_keep_fsh_c : forall i, 0 <= i < 8 ->
  aview SEGS (w_H W4) mem4 (nSH cx fp + i) = aview SEGS (w_H W3) memc (nSH cx fp + i).
Proof.
intros i Hi. pose proof HK4 as (_ & _ & _ & K4 & _). geo.
apply (K4 NX_CID fp _ hd_fin).
- right. unfold in_zr. cbn [fst snd]. rewrite <- hd_SH, hd_fsb. change (64 / 8) with 8. lia.
- unfold rread_wrset, SRC_FILE_BLOCK. intros [H|H]; lia.
Qed.

Lemma hd_keep_fsh : forall i, 0 <= i < 8 -> i <> 4 -> i <> 5 ->
  aview SEGS (w_H W4) mem4 (nSH cx fp + i) = aview SEGS (w_H W3) (ms_mem ms3) (nSH cx fp + i).
Proof.
intros i Hi H4 H5. rewrite (hd_keep_fsh_c i Hi). geo. apply HRUN; lia.
Qed.

Lemma hd_keep_cf : forall c p a, In (c, p) (frames (n_Sc cx)) ->
  (in_zr a (frame_rng (n_lyc cx) (c, p)) \/
   in_zr a (shadow_addr (frame_addr (n_lyc cx) c p), fs_frame_bytes c / 8)) ->
  ~ (n_h cx <= a < n_h cx + SRC_FILE_BLOCK) ->
  aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) (ms_mem ms3) a.
Proof.
intros c p a Hin Ha Hnh. pose proof HK4 as (_ & _ & _ & K4 & _).
pose proof (hd_fin_c c p Hin) as Hin3.
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 c p hd_AR Hin3) as (Hc1 & Hc2 & Hcapp).
rewrite hd_fa in Hc1, Hc2, Hcapp. pose proof (fs_frame_bytes_nonneg c) as Hfs0.
pose proof (hd_sep_cf c p Hin) as Dcf. pose proof (hd_sep_cfs c p Hin) as Dcfs. pose proof asan_consts as (C0 & _).
pose proof (shadow_addr_bounds (frame_addr (n_lyc cx) c p) ltac:(unfold in_app, ASAN_CEIL, kHighMemEnd in *; lia)) as Hsb1.
pose proof (shadow_range_end (frame_addr (n_lyc cx) c p) (fs_frame_bytes c) Hfs0) as Hse.
pose proof (shadow_addr_bounds (frame_addr (n_lyc cx) c p + fs_frame_bytes c)
  ltac:(unfold in_app, ASAN_CEIL, kHighMemEnd in *; lia)) as Hsb2.
unfold frame_rng, in_zr in Ha. cbn [fst snd] in Ha. geo.
unfold kLowMemEnd, kHighShadowEnd in *.
rewrite (K4 c p a Hin3).
- apply HRUN; destruct Ha; lia.
- unfold frame_rng, in_zr. cbn [fst snd]. rewrite hd_fa. exact Ha.
- unfold rread_wrset, SRC_FILE_BLOCK. intros [H|H]; [lia|]. unfold nF in *. destruct Ha; lia.
Qed.

Lemma hd_keep_blk : forall b m i, In (b, m) (ablocks B (n_lyc cx) (n_Sc cx)) -> 0 <= i < req_size m ->
  ~ (n_h cx <= b + i < n_h cx + SRC_FILE_BLOCK) ->
  aview SEGS (w_H W4) mem4 (b + i) = aview SEGS (w_H W3) (ms_mem ms3) (b + i).
Proof.
intros b m i Hin Hi Hnh. pose proof HK4 as (_ & K2 & _). rewrite <- HAB in Hin.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ hd_AR Hin) as (_ & Hb1 & Hb2 & Hbapp & _).
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 b m NX_CID fp hd_AR Hin hd_fin) as D.
unfold zdisjoint in D. cbn [fst snd] in D. rewrite hd_fa, hd_fsb in D. geo.
rewrite (K2 b m i Hin Hi).
- apply HRUN; lia.
- unfold rread_wrset, SRC_FILE_BLOCK. intros [H|H]; [lia|]. unfold nF in *. lia.
Qed.

Lemma hd_keep_img : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) ->
  aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) (ms_mem ms3) a.
Proof.
intros a Hi Hno He. pose proof HK4 as (_ & _ & K3 & _). pose proof (pa_segs_low a Hi) as Hlo. geo.
rewrite (K3 a Hi Hno He). unfold kLowMemEnd in Hlo. apply HRUN; lia.
Qed.

(* The caller's struct and timestamp cell lie in caller frames; their bytes and shadows are kept. *)
Lemma hd_keep_in_cf : forall c p x n, In (c, p) (n_own cx) ->
  frame_addr (n_lyc cx) c p <= x -> x + n <= frame_addr (n_lyc cx) c p + fs_frame_bytes c -> x mod 8 = 0 ->
  (x + n <= n_h cx \/ n_h cx + SRC_FILE_BLOCK <= x) ->
  (forall a, x <= a < x + n -> aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) (ms_mem ms3) a) /\
  (forall a, x <= a < x + n -> aview SEGS (w_H W4) mem4 (shadow_of_addr SHADOW_OFF a) =
     aview SEGS (w_H W3) (ms_mem ms3) (shadow_of_addr SHADOW_OFF a)).
Proof.
intros c p x n Hown Hx1 Hx2 Hx8 Hxh. pose proof (hd_cframes c p Hown) as Hin.
pose proof (hd_fin_c c p Hin) as Hin3.
pose proof (frame_al64 SEGS B ly3 S3 W3 (ms_mem ms3) md3 c p hd_AR Hin3) as (Ha64 & Hb64 & H64).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 c p hd_AR Hin3) as (Hc1 & Hc2 & Hcapp).
rewrite hd_fa in Ha64, Hc1, Hc2, Hcapp. pose proof asan_consts as (C0 & _).
pose proof (hd_hblk Hh) as (_ & Hh1 & Hh2 & Hhapp & _).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SRC_FILE_BLOCK in *.
split.
- intros a Ha. apply (hd_keep_cf c p a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia|].
  unfold SRC_FILE_BLOCK. lia.
- intros a Ha. apply (hd_keep_cf c p (shadow_of_addr SHADOW_OFF a) Hin).
  + right. unfold in_zr, shadow_addr, shadow_of_addr. cbn [fst snd].
    set (fa := frame_addr (n_lyc cx) c p) in *. set (fs := fs_frame_bytes c) in *.
    pose proof (Z.div_mod fa 64 ltac:(lia)) as Dfa. pose proof (Z.div_mod fs 64 ltac:(lia)) as Dfs.
    rewrite Ha64, Z.add_0_r in Dfa. rewrite Hb64, Z.add_0_r in Dfs.
    assert (E1 : fa / 8 = 8 * (fa / 64)) by (rewrite Dfa at 1; replace (64 * (fa / 64)) with (8 * (fa / 64) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
    assert (E2 : fs / 8 = 8 * (fs / 64)) by (rewrite Dfs at 1; replace (64 * (fs / 64)) with (8 * (fs / 64) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
    assert (fa / 8 <= a / 8) by (apply Z.div_le_mono; lia).
    assert (a / 8 < fa / 8 + fs / 8).
    { rewrite E1, E2. apply Z.div_lt_upper_bound; lia. }
    lia.
  + unfold shadow_of_addr, SHADOW_OFF, SRC_FILE_BLOCK.
    assert (a / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma hd_kept_nx : forall ly2 S2 md4,
  nx_kept SEGS NX_STK B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) W3 (ms_mem ms3) (spZ (n_regs cx)) (nx_E cx) ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly2 S2 W4 mem4 md4 k2 ->
  nx_kept SEGS NX_STK B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) W4 mem4 (spZ (n_regs cx)) (nx_E cx).
Proof.
intros ly2 S2 md4 (O1 & O2 & O3 & O4 & O5 & O6) HJ4.
pose proof HK4 as (K1 & _).
pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres4 & _).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwin & Hspsp0 & _).
assert (KST : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ (n_regs cx) - NX_STK <= a < spZ (n_regs cx)) ->
  aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha Hw. geo. rewrite (K1 a); [| lia | lia | unfold rread_wrset, SRC_FILE_BLOCK; intros [H|H]; lia].
  apply HRUN; lia. }
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hw HnE. rewrite (KST a Ha Hw). exact (O1 a Ha Hw HnE).
- intros b m i Hb Hi HnE. rewrite (hd_keep_blk b m i Hb Hi); [exact (O2 b m i Hb Hi HnE)|].
  intros H. apply HnE. unfold nx_E, nx_wrset. right. right. right. split; [exact Hh | exact H].
- intros a Hi Hno He. rewrite (hd_keep_img a Hi Hno He). exact (O3 a Hi Hno He).
- intros c p a Hin Hr HnE. rewrite (hd_keep_cf c p a Hin Hr); [exact (O4 c p a Hin Hr HnE)|].
  intros H. apply HnE. unfold nx_E, nx_wrset. right. right. right. split; [exact Hh | exact H].
- intros a Ha Hw Hp. pose proof (O5 a Ha Hw Hp) as Hp3. pose proof asan_consts as (C0 & _).
  eapply (apresent_transfer SEGS);
    [lia | intros Him; pose proof (pa_segs_low a Him); unfold kLowMemEnd in *; lia | exact (KST a Ha Hw) | exact Hp3].
- intros a Ha. apply Hpres4. lia.
Qed.


(* The machine state's facts the header phase carries, moved from NP_loop to NP_hd_ra. *)
Lemma hd_rw : forall a v, (forall i, 0 <= i < 8 -> aview SEGS (w_H W4) mem4 (a + i) =
                                              aview SEGS (w_H W3) (ms_mem ms3) (a + i)) ->
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) a = Some v -> rdword (aview SEGS (w_H W4) mem4) a = Some v.
Proof.
intros a v Hk Hr. rewrite (rdword_ext (aview SEGS (w_H W3) (ms_mem ms3)) (aview SEGS (w_H W4) mem4) a Hk). exact Hr.
Qed.

Lemma hd_rw_stack : forall a v, n_sp1 cx <= a -> a + 8 <= 2 ^ 64 ->
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) a = Some v -> rdword (aview SEGS (w_H W4) mem4) a = Some v.
Proof. intros a v H1 H2. apply hd_rw. intros i Hi. apply hd_keep_stack. lia. Qed.

Lemma hd_rw_frame : forall off v, 0 <= off -> off + 8 <= 32 \/ (48 <= off /\ off + 8 <= 64) ->
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (nF cx fp + off) = Some v ->
  rdword (aview SEGS (w_H W4) mem4) (nF cx fp + off) = Some v.
Proof.
intros off v H0 Hoff. apply hd_rw. intros i Hi. apply hd_keep_frame; unfold NO_PH, NX_PH_LEN; lia.
Qed.

Lemma hd_slot : forall (ms4 : machine_state) off v, ms_mem ms4 = mem4 -> 0 <= off <= 112 ->
  nslot cx W3 ms3 off v -> nslot cx W4 ms4 off v.
Proof.
intros ms4 off v Hm Hoff Hs. unfold nslot in *. rewrite Hm. pose proof hd_spf as (_ & Hsp2 & _ & Hsp4 & _).
apply hd_rw_stack; [lia | lia | exact Hs].
Qed.

Lemma hd_saved : forall (ms4 : machine_state), ms_mem ms4 = mem4 -> nsaved cx W3 ms3 -> nsaved cx W4 ms4.
Proof.
intros ms4 Hm (HS8 & HSj). unfold nsaved. rewrite Hm. pose proof hd_spf as (_ & Hsp2 & _ & Hsp4 & _).
split; [apply hd_rw_stack; [lia | lia | exact HS8]|].
intros j Hj. apply hd_rw_stack; [lia | lia | exact (HSj j Hj)].
Qed.

Lemma hd_header : forall (ms4 : machine_state), ms_mem ms4 = mem4 -> nheader cx fp W3 ms3 -> nheader cx fp W4 ms4.
Proof.
intros ms4 Hm (Hh0 & Hh8 & Hh16). unfold nheader. rewrite Hm.
split; [rewrite <- (Z.add_0_r (nF cx fp)); apply hd_rw_frame; [lia | lia | rewrite Z.add_0_r; exact Hh0]|].
split; [apply hd_rw_frame; [lia | lia | exact Hh8] | apply hd_rw_frame; [lia | lia | exact Hh16]].
Qed.

Lemma hd_flagw : forall (ms4 : machine_state), ms_mem ms4 = mem4 -> nflagw cx fp W3 ms3 -> nflagw cx fp W4 ms4.
Proof.
intros ms4 Hm HF. unfold nflagw in *. rewrite Hm. apply hd_rw_frame; [unfold NX_FLAGPTR; lia | unfold NX_FLAGPTR; lia | exact HF].
Qed.

Lemma hd_slots : forall (ms4 : machine_state), ms_mem ms4 = mem4 -> nslots cx fp W3 ms3 -> nslots cx fp W4 ms4.
Proof.
intros ms4 Hm (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11). unfold nslots.
repeat match goal with |- _ /\ _ => split end.
all: apply (hd_slot ms4); [exact Hm | unfold NS_F0, NS_FK, NS_TS, NS_SB, NS_PS8, NS_PS12, NS_SH8, NS_SH12, NS_OFF8, NS_OFF12, NS_MASK; lia | assumption].
Qed.

Lemma hd_shadow : forall (ms4 : machine_state), ms_mem ms4 = mem4 ->
  aview SEGS (w_H W3) memc (nSH cx fp + 4) = Some 0 -> aview SEGS (w_H W3) memc (nSH cx fp + 5) = Some 0 ->
  nshadow cx fp W3 ms3 NSH_entry -> nshadow cx fp W4 ms4 NSH_ph.
Proof.
intros ms4 Hm H4 H5 HSH i Hi. rewrite Hm. change (length NSH_ph) with 8%nat in Hi.
destruct (Nat.eq_dec i 4) as [->|N4].
{ change (Z.of_nat 4) with 4. rewrite (hd_keep_fsh_c 4 ltac:(lia)). exact H4. }
destruct (Nat.eq_dec i 5) as [->|N5].
{ change (Z.of_nat 5) with 5. rewrite (hd_keep_fsh_c 5 ltac:(lia)). exact H5. }
rewrite (hd_keep_fsh (Z.of_nat i) ltac:(lia) ltac:(lia) ltac:(lia)).
rewrite (HSH i ltac:(cbn; lia)). f_equal.
assert (Hi' : (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 6 \/ i = 7)%nat) by lia.
destruct Hi' as [-> | [-> | [-> | [-> | [-> | ->]]]]]; reflexivity.
Qed.

(* The caller's struct, its shadow, the record buffer and the timestamp cell. *)
Lemma hd_ps : forall sw ol vt vid pad,
  nx_ps_at SEGS (rdW W3 (ms_mem ms3)) (n_ps cx) (n_h cx) sw ol vt vid pad ->
  range_addressable (aview SEGS (w_H W3) (ms_mem ms3)) SHADOW_OFF (n_ps cx) PS_LEN ->
  nx_ps_at SEGS (rdW W4 mem4) (n_ps cx) (n_h cx) sw ol vt vid pad /\
  range_addressable (aview SEGS (w_H W4) mem4) SHADOW_OFF (n_ps cx) PS_LEN.
Proof.
intros sw ol vt vid pad (V0 & V8 & V12 & V16 & V20 & Vpad & Lpad) HRA.
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hps8 & _ & _ & _
  & Hcown & Hcf1 & Hcf2 & _ & _ & _ & _ & _ & _ & _ & Hstr & _).
destruct (Hstr Hh) as (_ & _ & _ & _ & _ & _ & _ & Hpsh & _).
pose proof (hd_keep_in_cf (n_cid cx) (n_pos cx) (n_ps cx) PS_LEN Hcown Hcf1 Hcf2 Hps8 Hpsh) as (KPS & KPSS).
clear Hstr Hpsh.
assert (KPSb : forall x, n_ps cx <= x < n_ps cx + 24 ->
  mbyte SEGS (rdW W4 mem4) x = mbyte SEGS (rdW W3 (ms_mem ms3)) x)
  by (intros x Hx; apply (mbyte_of_aview SEGS); apply KPS; unfold PS_LEN; lia).
assert (VF : forall off n v, 0 <= off -> off + Z.of_nat n <= 24 ->
  val_mem SEGS (rdW W3 (ms_mem ms3)) (n_ps cx + off) n v -> val_mem SEGS (rdW W4 mem4) (n_ps cx + off) n v).
{ intros off n v H0 Hn Hv. eapply (PcapSourceClose.vm_frame _ _ _ _ _ _ Hv). Unshelve.
  intros x Hx. apply KPSb. lia. }
split.
- unfold nx_ps_at. split; [apply VF; [unfold PS_F_OFF; lia | cbn; unfold PS_F_OFF; lia | exact V0]|].
  split; [apply VF; [unfold PS_SW_OFF; lia | cbn; unfold PS_SW_OFF; lia | exact V8]|].
  split; [apply VF; [unfold PS_OL_OFF; lia | cbn; unfold PS_OL_OFF; lia | exact V12]|].
  split; [apply VF; [unfold PS_VT_OFF; lia | cbn; unfold PS_VT_OFF; lia | exact V16]|].
  split; [apply VF; [unfold PS_VID_OFF; lia | cbn; unfold PS_VID_OFF; lia | exact V20]|].
  split; [|exact Lpad].
  apply (garr8_frame SEGS _ _ _ _ Vpad). intros x Hx. rewrite Lpad in Hx. cbn [Z.of_nat Pos.of_succ_nat] in Hx.
  apply KPSb. lia.
- apply (PcapSourceCloseSpec.ra_frame _ _ _ _ HRA). intros x Hx. apply KPSS. exact Hx.
Qed.

Lemma hd_buf : forall bj', garr8 SEGS (rdW W3 (ms_mem ms3)) (n_buf cx) bj' -> length bj' = length (n_bj cx) ->
  garr8 SEGS (rdW W4 mem4) (n_buf cx) bj'.
Proof.
intros bj' Hgb Hlb.
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & _ & _ & _ & _ & _ & _ & _ & _ & Hbuf & _ & Hstr & _).
destruct (Hbuf Hh) as (Hbin & _ & _ & _ & Hlbj & _ & _ & _).
destruct (Hstr Hh) as (_ & _ & _ & _ & _ & Hbh & _).
clear Hbuf Hstr.
pose proof (req_size_pos (nx_bufn (n_cap cx)) ltac:(unfold nx_bufn; lia)) as [_ Hq].
apply (garr8_frame SEGS _ _ _ _ Hgb). intros x Hx. apply (mbyte_of_aview SEGS).
rewrite Hlb in Hx. replace x with (n_buf cx + (x - n_buf cx)) by lia.
apply (hd_keep_blk _ _ _ Hbin); [lia|]. unfold SRC_FILE_BLOCK in *. lia.
Qed.

Lemma hd_ts : forall tv, n_ts cx <> 0 ->
  val_mem SEGS (rdW W3 (ms_mem ms3)) (n_ts cx) 8 tv ->
  range_addressable (aview SEGS (w_H W3) (ms_mem ms3)) SHADOW_OFF (n_ts cx) 8 ->
  val_mem SEGS (rdW W4 mem4) (n_ts cx) 8 tv /\
  range_addressable (aview SEGS (w_H W4) mem4) SHADOW_OFF (n_ts cx) 8.
Proof.
intros tv Hts0 Vts RAts.
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hts & Hstr & _).
destruct (Hts Hh Hts0) as (_ & Hts8 & _ & _ & _ & (tc & tp & Htown & Ht1 & Ht2) & _).
destruct (Hstr Hh) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Htsh & _).
destruct (Htsh Hts0) as (Htsh' & _).
pose proof (hd_keep_in_cf tc tp (n_ts cx) 8 Htown Ht1 Ht2 Hts8 Htsh') as (KT & KTS).
clear Hts Hstr Htsh.
split.
- eapply (PcapSourceClose.vm_frame _ _ _ _ _ _ Vts). Unshelve. intros x Hx. apply (mbyte_of_aview SEGS). apply KT. cbn in Hx. lia.
- apply (PcapSourceCloseSpec.ra_frame _ _ _ _ RAts). intros x Hx. apply KTS. exact Hx.
Qed.

(* NP_hd_ra: the landing. From the loop head's invariant, the run's state at the call, and the fread's
   post, the entry predicate of the header phase (PcapSourceNextHdrBDefs.v's nx_hdra_inv). *)
Lemma hd_land : forall R q lh (regsc : bvmap 5 word) mdc ly2 S2 (regs4 : bvmap 5 word) md4,
  nx_next_ok R cx q ->
  nx_loop_inv B MT KS cx fp q lh k2 ly3 S3 W3 ms3 md3 ->
  aregs_preserved (ms_regs ms3) regsc ->
  aview SEGS (w_H W3) memc (nSH cx fp + 4) = Some 0 -> aview SEGS (w_H W3) memc (nSH cx fp + 5) = Some 0 ->
  m_fds mdc = m_fds md3 -> m_fs mdc = m_fs md3 ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly2 S2 W4 mem4 md4 k2 ->
  aregs_preserved regsc regs4 ->
  afread_post SEGS KS (nF cx fp + NO_PH) NX_PH_LEN (n_h cx) (n_b cx) q (n_C cx) ly3 S3 W3 memc mdc
    ly2 S2 W4 regs4 mem4 md4 ->
  nx_hdra_inv B MT KS R cx fp k2 ly3 S3 W4 (mkst regs4 (Z_to_bv 64 (BASE + NP_hd_ra)) mem4 (seg_rom SEGS)) md4.
Proof.
intros R q lh regsc mdc ly2 S2 regs4 md4 HR HL HP1 H4 H5 Hfd1 Hfs1 HJ4 HP2 HQ.
destruct HQ as (-> & -> & R10 & HG & HSRC4 & _ & _ & Hfd2 & Hfs2 & _).
destruct HL as (HM & R20 & R21 & R23 & R26 & HCH).
destruct HM as (HBD & R24 & HJB & HK3 & _ & _ & HPS & HPSRA & HSRC & Hq & HBUF & HTS).
destruct HBD as (HB0 & HSL).
destruct HB0 as (Hpc & Hresv & Hpend & Hrom & Hfr & Hfc & HRG & HSV & HHD & HFW & HSHD & Hlen & R18 & R19 & HF0).
destruct HRG as (R2 & R8 & R9 & R3 & R4).
destruct HJB as (Hk2 & HAB' & Hmo & Hfds3 & Hfs3).
assert (PR : forall r, acallee_saved r -> getr regs4 (Z_to_bv 5 r) = getr (ms_regs ms3) (Z_to_bv 5 r))
  by (intros r Hr; rewrite (HP2 r Hr); exact (HP1 r Hr)).
set (ms4 := mkst regs4 (Z_to_bv 64 (BASE + NP_hd_ra)) mem4 (seg_rom SEGS)).
assert (Hm4 : ms_mem ms4 = mem4) by reflexivity.
destruct (hd_ps _ _ _ _ _ HPS HPSRA) as (HPS4 & HPSRA4).
exists q, lh. split; [exact HR|].
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
- (* nx_mid *)
  unfold nx_mid. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]]].
  + (* nx_body *)
    split.
    * unfold nx_body0.
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|].
      split.
      { unfold nregs. subst ms4. cbn [ms_regs mkst].
        split; [rewrite <- R2; exact (PR 2 ltac:(unfold acallee_saved; lia))|].
        split; [rewrite <- R8; exact (PR 8 ltac:(unfold acallee_saved; lia))|].
        split; [rewrite <- R9; exact (PR 9 ltac:(unfold acallee_saved; lia))|].
        split; [rewrite <- R3; exact (PR 3 ltac:(unfold acallee_saved; lia))|].
        rewrite <- R4; exact (PR 4 ltac:(unfold acallee_saved; lia)). }
      split; [exact (hd_saved ms4 Hm4 HSV)|].
      split; [exact (hd_header ms4 Hm4 HHD)|].
      split; [exact (hd_flagw ms4 Hm4 HFW)|].
      split; [exact (hd_shadow ms4 Hm4 H4 H5 HSHD)|].
      split; [reflexivity|].
      split; [subst ms4; cbn [ms_regs mkst]; rewrite <- R18; exact (PR 18 ltac:(unfold acallee_saved; lia))|].
      split; [subst ms4; cbn [ms_regs mkst]; rewrite <- R19; exact (PR 19 ltac:(unfold acallee_saved; lia))|].
      apply (hd_slot ms4); [exact Hm4 | unfold NS_F0; lia | exact HF0].
    * exact (hd_slots ms4 Hm4 HSL).
  + subst ms4. cbn [ms_regs mkst]. rewrite <- R24. exact (PR 24 ltac:(unfold acallee_saved; lia)).
  + unfold nx_jbk. split; [exact Hk2|]. split; [exact HAB'|]. split; [exact Hmo|].
    split; [rewrite Hfd2, Hfd1; exact Hfds3 | rewrite Hfs2, Hfs1; exact Hfs3].
  + rewrite Hm4. exact (hd_kept_nx ly3 S3 md4 HK3 HJ4).
  + intros a Ha. exact Ha.
  + exact Hh.
  + rewrite Hm4. exact HPS4.
  + rewrite Hm4. exact HPSRA4.
  + rewrite Hm4. exact HSRC4.
  + unfold nx_hk, NX_PH_LEN. lia.
  + rewrite Hm4. destruct HBUF as (bj' & Hgb & Hlb). exists bj'. split; [exact (hd_buf bj' Hgb Hlb) | exact Hlb].
  + intros Hts0. rewrite Hm4. destruct (HTS Hts0) as (Vts & RAts). exact (hd_ts _ Hts0 Vts RAts).
- subst ms4. cbn [ms_regs mkst]. exact R10.
- rewrite Hm4. exact HG.
- subst ms4. cbn [ms_regs mkst]. rewrite <- R20. exact (PR 20 ltac:(unfold acallee_saved; lia)).
- subst ms4. cbn [ms_regs mkst]. rewrite <- R21. exact (PR 21 ltac:(unfold acallee_saved; lia)).
- subst ms4. cbn [ms_regs mkst]. rewrite <- R23. exact (PR 23 ltac:(unfold acallee_saved; lia)).
- subst ms4. cbn [ms_regs mkst]. rewrite <- R26. exact (PR 26 ltac:(unfold acallee_saved; lia)).
- exact Hq.
- exact HCH.
Qed.

End f.

End d.

(* ---- the phase lemma ---- *)

(* The shadow byte of an 8-aligned, 8-byte-addressable word is 0 (saddr_ok at its last byte). *)
Lemma hd_sh0 : forall (rd : Z -> option Z) ps, ps mod 8 = 0 ->
  range_addressable rd SHADOW_OFF ps 8 -> rd (shadow_of_addr SHADOW_OFF ps) = Some 0.
Proof.
intros rd ps Hal HR. destruct (HR (ps + 7) ltac:(lia)) as (s & Hs & Hok).
rewrite (shadow_of_addr_aligned_off SHADOW_OFF ps 7 Hal) in Hs.
change (7 / 8) with 0 in Hs. rewrite Z.add_0_r in Hs. rewrite Hs. f_equal.
unfold saddr_ok in Hok. destruct Hok as [-> | [H1 H2]]; [reflexivity|].
exfalso. assert (Hm7 : (ps + 7) mod 8 = 7) by (rewrite <- Zplus_mod_idemp_l, Hal; reflexivity). lia.
Qed.

Hypothesis ASIL : asource_img_laws SK SEGS B KS.
Hypothesis AFREAD : afread_spec SK SEGS B KS (SIGMA PS___interceptor_trampoline_fread).

Theorem pb_hdA : forall R : ncx -> Z -> Prop,
  nx_from SK B KS (nx_post SK B MT KS) (nx_hdra_inv B MT KS R) ->
  nx_from SK B KS (nx_post SK B MT KS)
    (fun cx fp k2 ly3 S3 W3 ms3 md3 =>
       exists q lh, nx_next_ok R cx q /\ nx_loop_inv B MT KS cx fp q lh k2 ly3 S3 W3 ms3 md3).
Proof.
intros R HN cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR (q & lh & HR & HL).
pose proof HL as (HM & R20 & R21 & R23 & R26 & HCH).
pose proof HM as (HBD & R24 & HJB & HK3 & HEsub & Hh & HPS & HPSRA & HSRC & Hq & HBUF & HTS).
pose proof HJB as (Hk2 & HAB & Hmo & Hfds & Hfs).
pose proof HBD as (HB0 & HSL).
pose proof HB0 as (Hpc & Hresv & Hpend & Hrom & Hfr & Hfc & HRG & HSV & HHD & HFW & HSHD & Hlen & R18 & R19 & HF0).
pose proof HRG as (R2 & R8 & R9 & R3 & R4).
pose proof (hd_Ff cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR) as (HF1 & HF2 & HF64 & HFapp).
pose proof (hd_spf cx HB) as (Hsp1 & Hsp2 & Hsp3 & Hsp4 & Hsp5).
pose proof (hd_SH cx fp k2 ly3 S3 W3 ms3 md3 HB HJ) as HSHeq.
pose proof (hd_fin cx fp S3 HFR) as Hfin.
pose proof (hd_AR cx fp k2 ly3 S3 W3 ms3 md3 HJ) as HAR.
pose proof (hd_fa cx fp k2 ly3 S3 W3 ms3 md3 HB HJ) as HFA.
pose proof (hd_hblk cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR HAB Hh) as (Hhin & Hh1 & Hh2 & Hhapp & Hhd).
pose proof asan_consts as (C0 & _).
pose proof HB as (HJ0 & HROD & Hra & Hra4 & Hgp & Htp & _ & _ & _ & _ & Hal16 & Hwin & Hspsp0 & HCHAIN & _
  & Hpsf & Hh64 & Hps8 & Hps4096 & Hps47 & Hpsam & Hcown & Hcf1 & Hcf2 & HPSRA0 & _ & _ & _ & _ & Hbuf & Hts
  & Hstr & _).
destruct (Hstr Hh) as (Hhin0 & Hbin0 & HSRC0 & HClen & Hp0 & Hbh & Hbb & Hpsh & Hpsb & Htsh & HFPinc).
assert (HM8 : forall z, z mod 64 = 0 -> z mod 8 = 0).
{ intros z Hz. apply Z.mod_divide in Hz; [|lia]. apply Z.mod_divide; [lia|].
  destruct Hz as [u Hu]. exists (8 * u). lia. }
assert (HF8 : nF cx fp mod 8 = 0) by (apply HM8; exact HF64).
(* ps and the frame are apart: ps lies in a caller frame *)
assert (Hpsf2 : n_ps cx + 8 <= nF cx fp \/ nF cx fp + 64 <= n_ps cx).
{ destruct (hd_sep_cf cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR (n_cid cx) (n_pos cx)
    (hd_cframes cx HB _ _ Hcown)) as [D|D]; [right; lia | left; unfold PS_LEN in *; lia]. }
(* the shadow byte of ps is 0 *)
assert (HSH0 : aview SEGS (w_H W3) (ms_mem ms3) (shadow_of_addr SHADOW_OFF (n_ps cx)) = Some 0).
{ apply (hd_sh0 _ _ Hps8). eapply range_addressable_sub; [exact HPSRA | lia | unfold PS_LEN; lia]. }
assert (Hpsv : val_mem SEGS (rdW W3 (ms_mem ms3)) (n_ps cx) 8 (n_h cx)).
{ pose proof HPS as (V0 & _). unfold PS_F_OFF in V0. rewrite Z.add_0_r in V0. exact V0. }
assert (HFlo : 0 <= nF cx fp) by (clear - HF1; lia).
assert (HFhi : nF cx fp + 64 <= 2 ^ 47) by (clear - HF2 C0; lia).
assert (HPSb : 0 <= n_ps cx /\ n_ps cx + 8 <= 2 ^ 47) by (clear - Hps4096 Hps47; unfold PS_LEN in *; lia).
assert (HPSam : amem_range (n_ps cx) 8)
  by (clear - Hpsam; unfold amem_range, PS_LEN, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
assert (HPR4 : apresent (w_H W3) (ms_mem ms3) (shadow_of_addr SHADOW_OFF (nF cx fp) + 4)).
{ destruct (al_frames _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 NX_CID fp HAR Hfin) as (_ & _ & _ & Hsh).
  rewrite hd_fsb in Hsh. destruct (Hsh 4 ltac:(change (64 / 8) with 8; lia)) as [Hpr _].
  rewrite <- HSHeq in Hpr. exact Hpr. }
assert (HPR5 : apresent (w_H W3) (ms_mem ms3) (shadow_of_addr SHADOW_OFF (nF cx fp) + 5)).
{ destruct (al_frames _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 NX_CID fp HAR Hfin) as (_ & _ & _ & Hsh).
  rewrite hd_fsb in Hsh. destruct (Hsh 5 ltac:(change (64 / 8) with 8; lia)) as [Hpr _].
  rewrite <- HSHeq in Hpr. exact Hpr. }
eapply (hd_to_call W3 ms3 md3 (n_h cx) (nF cx fp) (n_ps cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
  (n_W0 cx) (n_mem0 cx) (n_md0 cx) (n_own cx) ly3 S3 k2 fp (nx_post SK B MT KS cx) HJ (eq_sym HSHeq)
  Hpc Hresv Hpend Hrom Hfr Hfc R19 R24 R21 Hh64 HF8 HFlo HFhi Hps8 HPSb HPSam
  Hpsf2 HPR4 HPR5 HSH0 Hpsv).
(* at the fread wrapper's entry *)
  intros regsc memc mdc HJc HPc Q1 Q10 Q11 Q12 Q13 HRUN H4 H5 Hfdc Hfsc.
  assert (Q2 : getr regsc 2 = getr (ms_regs ms3) 2) by exact (HPc 2 ltac:(unfold acallee_saved; lia)).
  assert (Q8 : getr regsc 8 = getr (ms_regs ms3) 8) by exact (HPc 8 ltac:(unfold acallee_saved; lia)).
  assert (Q3 : getr regsc 3 = getr (ms_regs ms3) 3) by exact (HPc 3 ltac:(unfold acallee_saved; lia)).
  assert (Q4 : getr regsc 4 = getr (ms_regs ms3) 4) by exact (HPc 4 ltac:(unfold acallee_saved; lia)).
  assert (Hspc : spZ regsc = n_sp1 cx).
  { unfold spZ. rewrite Q2, R2. apply unsigned_lit_small. clear - Hsp1 Hsp2 Hsp4 C0; unfold NX_STK, AFREAD_STK in *; lia. }
  assert (Hs0c : s0Z regsc = spZ (n_regs cx)).
  { unfold s0Z. rewrite Q8, R8. apply unsigned_lit_small. clear - Hsp1 Hsp2 C0; unfold NX_STK, AFREAD_STK in *; lia. }
  assert (Hrac : raZ regsc = pa_val A_TEXT + NP_hd_ra).
  { unfold raZ. rewrite Q1. apply unsigned_lit_small. pose proof pa_B_ok as (HB0' & HB1' & _).
    unfold NP_hd_ra. lia. }
  pose proof pa_base_lo as HBLO.
  (* the memory at the call, above the entry sp, is the caller's *)
  assert (HUP : forall a, spZ (n_regs cx) <= a < 2 ^ 64 ->
    aview SEGS (w_H W3) memc a = aview SEGS (w_H (n_W cx)) (n_memc cx) a).
  { intros a Ha. pose proof hd_SHr as HSHr.
    assert (HSHr' : SHADOW_OFF + 512 <= nSH cx fp /\ nSH cx fp + 8 <= kHighMemBeg)
      by exact (HSHr cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR).
    destruct HSHr' as (HS1 & HS2).
    rewrite (HRUN a ltac:(clear - Ha Hsp1 C0; unfold NX_STK, AFREAD_STK in *; lia)
      ltac:(clear - Ha Hsp1 HS2 C0; unfold nSH, kHighMemBeg, NX_STK, AFREAD_STK in *; lia)
      ltac:(clear - Ha Hsp1 HS2 C0; unfold nSH, kHighMemBeg, NX_STK, AFREAD_STK in *; lia)).
    destruct (Hbuf Hh) as (Hbin1 & _).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ (proj1 HJ0) Hbin1) as (_ & _ & Hbc & _).
    pose proof (req_size_pos (nx_bufn (n_cap cx)) ltac:(clear; unfold nx_bufn; lia)) as [_ Hq2].
    assert (HTSc : n_ts cx <> 0 -> n_ts cx + 8 <= alloc_ceiling).
    { intros Hne. destruct (Hts Hh Hne) as (_ & _ & _ & _ & _ & (tc & tp & Htown & Ht1 & Ht2) & _).
      destruct (frames_bounds SEGS B LAWS _ _ _ _ _ tc tp (proj1 HJ0) (hd_cframes cx HB _ _ Htown)) as (_ & Htc & _).
      pose proof (fs_frame_bytes_nonneg tc). clear - Ht1 Ht2 Htc. lia. }
    assert (HPSc : n_ps cx + PS_LEN <= alloc_ceiling).
    { destruct (frames_bounds SEGS B LAWS _ _ _ _ _ (n_cid cx) (n_pos cx) (proj1 HJ0)
        (hd_cframes cx HB _ _ Hcown)) as (_ & Hpc2 & _).
      pose proof (fs_frame_bytes_nonneg (n_cid cx)). clear - Hcf1 Hcf2 Hpc2. lia. }
    pose proof HK3 as (K1 & _). apply K1.
    - clear - Ha Hsp1 C0; unfold NX_STK, AFREAD_STK in *; lia.
    - clear - Ha Hsp1 C0; unfold NX_STK, AFREAD_STK in *; lia.
    - unfold nx_E, nx_wrset.
      clear - Ha Hsp1 C0 Hps4096 HPSc Hbc Hq2 HTSc Hh1 Hh2.
      unfold PS_LEN, SRC_FILE_BLOCK, NX_STK, AFREAD_STK in *.
      intros [Hw|[Hw|[Hw|Hw]]]; [lia | lia | destruct Hw as (Hne & Hw); specialize (HTSc Hne); lia | lia]. }
  (* the saved ra and s0 at the call *)
  assert (HSAV : rdword (aview SEGS (w_H W3) memc) (spZ (n_regs cx) - 8) = Some (raZ (n_regs cx)) /\
                 rdword (aview SEGS (w_H W3) memc) (spZ (n_regs cx) - 16) = Some (s0Z (n_regs cx))).
  { pose proof hd_SHr as HSHr.
    destruct (HSHr cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR) as (HS1 & HS2).
    pose proof HSV as (HS8 & HSj). pose proof (HSj 0 ltac:(lia)) as HS16.
    rewrite Z.mul_0_r, Z.sub_0_r in HS16. cbn [Z.ltb] in HS16.
    assert (EXT : forall d, -16 <= d <= -8 -> forall i, 0 <= i < 8 ->
      aview SEGS (w_H W3) memc (spZ (n_regs cx) + d + i) = aview SEGS (w_H W3) (ms_mem ms3) (spZ (n_regs cx) + d + i)).
    { intros d Hd i Hi. apply HRUN;
        clear - Hd Hi Hsp1 Hsp2 HS1 HS2 C0; unfold nSH, SHADOW_OFF, kHighMemBeg, NX_STK, AFREAD_STK in *; lia. }
    split.
    - rewrite (rdword_ext (aview SEGS (w_H W3) (ms_mem ms3)) (aview SEGS (w_H W3) memc) (spZ (n_regs cx) - 8)
        ltac:(intros i Hi; replace (spZ (n_regs cx) - 8 + i) with (spZ (n_regs cx) + (-8) + i) by lia;
              exact (EXT (-8) ltac:(lia) i Hi))).
      exact HS8.
    - rewrite (rdword_ext (aview SEGS (w_H W3) (ms_mem ms3)) (aview SEGS (w_H W3) memc) (spZ (n_regs cx) - 16)
        ltac:(intros i Hi; replace (spZ (n_regs cx) - 16 + i) with (spZ (n_regs cx) + (-16) + i) by lia;
              exact (EXT (-16) ltac:(lia) i Hi))).
      first [exact HS16 | (unfold s0Z; rewrite <- HS16; do 3 f_equal; apply bv_eq; reflexivity)]. }
  destruct HSAV as (HSA8 & HSA16).
  (* the call chain *)
  assert (HCHc : achain ly3 (aview SEGS (w_H W3) memc) (spZ regsc) (s0Z regsc) (nx_ch cx)).
  { rewrite Hspc, Hs0c. unfold nx_ch.
    pose proof (hd_top cx fp k2 ly3 S3 W3 ms3 md3 HB HJ) as HTOP.
    pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk0 & _).
    pose proof Hstk0 as (_ & _ & Hceil0 & Hslo0 & Hshi0 & H47 & _ & Htop1 & Htop2).
    pose proof HJ0 as (_ & Hly0 & _).
    pose proof Hly0 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop0 & Eslo0 & Eshi0 & _).
    assert (HT64 : ly_top ly3 <= 2 ^ 64) by (rewrite HTOP, Etop0; clear - H47 Htop2; lia).
    assert (HT16 : spZ (n_regs cx) mod 8 = 0).
    { pose proof Hal16 as Hal16'. apply Z.mod_divide in Hal16'; [|lia]. apply Z.mod_divide; [lia|].
      destruct Hal16' as [u Hu]. exists (2 * u). clear - Hu; lia. }
    destruct (Z.ltb_spec (spZ (n_regs cx) + 16) (ly_top (n_lyc cx))) as [Hlt | Hge].
    - eapply (achain_push ly3 (aview SEGS (w_H (n_W cx)) (n_memc cx)) (aview SEGS (w_H W3) memc)
        (spZ (n_regs cx)) (s0Z (n_regs cx)) (raZ (n_regs cx)) (n_ch cx) (n_sp1 cx)).
      + apply (achain_ly_top (n_lyc cx) ly3 _ _ _ _ HTOP). exact HCHAIN.
      + exact HT64.
      + intros a Ha. apply HUP. clear - Ha; lia.
      + exact HSA8.
      + exact HSA16.
      + exact Hra4.
      + clear - Hsp1 C0; unfold NX_STK, AFREAD_STK in *; lia.
      + exact HT16.
      + rewrite HTOP. clear - Hlt; lia.
      + clear - Hsp4; lia.
    - left. split; [right; left; rewrite HTOP; clear - Hge; lia | reflexivity]. }
  (* the stream at the call *)
  assert (HSRCc : asource_at SEGS KS (rdW W3 memc) (n_h cx) (n_b cx) (n_C cx) q).
  { pose proof hd_SHr as HSHr.
    destruct (HSHr cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR) as (HS1 & HS2).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ (proj1 HJ0) Hbin0) as (_ & Hb1 & Hb2 & Hbapp & _).
    pose proof (req_size_pos (Z.of_nat (length (n_C cx))) ltac:(clear; lia)) as [_ Hq2].
    assert (OUT : forall a, (n_h cx <= a < n_h cx + SRC_FILE_BLOCK) \/
      (n_b cx <= a < n_b cx + Z.of_nat (length (n_C cx))) \/ asrc_env_addr KS a ->
      0 <= a < 2 ^ 64 /\ (a < SHADOW_OFF \/ kHighMemBeg <= a)).
    { intros a Ha. destruct Ha as [Ha|[Ha|Ha]].
      - clear - Ha Hhapp Hh2 C0. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SRC_FILE_BLOCK, SHADOW_OFF in *. lia.
      - clear - Ha Hbapp Hb2 Hq2 C0. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
      - destruct (asil_env _ _ _ _ ASIL a Ha) as (Hi & _). pose proof (pa_img_range a Hi) as Hr.
        clear - Hr. unfold pcap_img_end, YImgTop.IMG_TOP, YImgTop.IMG_LO, SHADOW_OFF, kHighMemBeg in *. lia. }
    apply (PcapSourceClose.asource_at_frame KS (rdW W3 (ms_mem ms3)) (rdW W3 memc)); [|exact HSRC].
    intros a Ha. destruct (OUT a Ha) as (Hr1 & Hr2). apply (mbyte_of_aview SEGS). apply HRUN;
      [exact Hr1 | clear - Hr2 HS1 HS2; unfold nSH, SHADOW_OFF, kHighMemBeg in *; lia
      | clear - Hr2 HS1 HS2; unfold nSH, SHADOW_OFF, kHighMemBeg in *; lia]. }
  (* the shadow of the header in the call's memory *)
  assert (HRAd : range_addressable (aview SEGS (w_H W3) memc) SHADOW_OFF (nF cx fp + NO_PH) NX_PH_LEN)
    by (apply (hd_ph_ra _ (nF cx fp) HF8); [exact H4 | exact H5]).
  assert (HHULL : shadow_hull_vis (aview SEGS (w_H W3) memc) (nF cx fp + NO_PH) NX_PH_LEN).
  { pose proof (shadow_hull_vis_of_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 NX_CID fp
      (nF cx fp + NO_PH) NX_PH_LEN HAR Hfin ltac:(unfold NO_PH, nF; rewrite HFA; clear; lia)
      ltac:(unfold NO_PH, NX_PH_LEN, nF; rewrite HFA, hd_fsb; clear; lia) ltac:(unfold NX_PH_LEN; clear; lia)) as HV.
    intros s Hs. destruct (Z.eq_dec s (shadow_of_addr SHADOW_OFF (nF cx fp) + 4)) as [->|N4]; [rewrite H4; discriminate|].
    destruct (Z.eq_dec s (shadow_of_addr SHADOW_OFF (nF cx fp) + 5)) as [->|N5]; [rewrite H5; discriminate|].
    rewrite HRUN; [exact (HV s Hs) | | exact N4 | exact N5].
    clear - Hs HF1 HF2 C0. unfold shadow_addr, NO_PH, NX_PH_LEN, SHADOW_OFF in *.
    assert (A1 : 0 <= (nF cx fp + 32) / 8) by (apply Z.div_pos; lia).
    assert (A2 : 0 <= (2147450880 + (nF cx fp + 32) / 8) / 8) by (apply Z.div_pos; lia).
    assert (A3 : (2147450880 + (nF cx fp + 32 + 16 - 1) / 8) / 8 * 8 <= 2147450880 + (nF cx fp + 32 + 16 - 1) / 8)
      by (rewrite Z.mul_comm; apply Z.mul_div_le; lia).
    assert (A4 : (nF cx fp + 32 + 16 - 1) / 8 <= nF cx fp + 47) by (apply Z.div_le_upper_bound; lia).
    lia. }
  (* the call *)
  eapply SRr_bind.
  { eapply (AFREAD (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
      ((NX_CID, fp) :: n_own cx) ly3 S3 W3 memc mdc k2 regsc (nx_ch cx)
      (nF cx fp + NO_PH) NX_PH_LEN (n_h cx) (n_b cx) q (n_C cx)).
    unfold afread_pre, rread_call. 
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]]].
    - split; [exact HJc|].
      split; [rewrite Q1; apply ret_ok_codeptr_v; [unfold NP_hd_ra; lia | reflexivity]|].
      split; [rewrite Hrac; unfold NP_hd_ra; lia|].
      split; [rewrite Q3, R3; exact Hgp|].
      split; [rewrite Q4, R4; exact Htp|].
      split; [rewrite Hspc; pose proof Hsp5 as H5'; apply Z.mod_divide in H5'; [|clear; lia];
              apply Z.mod_divide; [clear; lia|]; destruct H5' as [u Hu]; exists (2 * u); clear - Hu; lia|].
      split; [rewrite Hspc; unfold NX_STK in *; lia|].
      split; [rewrite Hspc; lia|].
      exact HCHc.
    - rewrite Q10. exact R26.
    - exact Q11.
    - exact Q12.
    - exact Q13.
    - exact Hhin.
    - rewrite HAB. exact Hbin0.
    - left. rewrite Hspc. destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ (proj1 HJ0) Hbin0) as (_ & _ & Hbc & _).
      pose proof (req_size_pos (Z.of_nat (length (n_C cx))) ltac:(lia)) as [_ Hq2].
      unfold NX_STK in *. lia.
    - exact HSRCc.
    - (* the right to write the FILE block *)
      intros a Ha. split.
      + destruct (HFPinc a ltac:(exists (n_h cx, n_h cx + SRC_FILE_BLOCK); split; [left; reflexivity|cbn; lia]))
          as [Hin|Htmp].
        * right. left. split; [exact Hin|]. exists (n_h cx), SRC_FILE_BLOCK. split; [rewrite HAB; exact Hhin0|].
          change (req_size SRC_FILE_BLOCK) with SRC_FILE_BLOCK. exact Ha.
        * right. right. left. apply (in_tmp_block_mono _ (ablocks B (n_lyc cx) (n_Sc cx))); [|exact Htmp].
          intros x Hx. rewrite HAB. exact Hx.
      + rewrite Hspc. unfold SRC_FILE_BLOCK in *. unfold NX_STK in *. lia.
    - unfold NX_PH_LEN. lia.
    - (* the destination *)
      split; [unfold NO_PH, NX_PH_LEN, SRC_FILE_BLOCK in *; lia|].
      split; [pose proof (hd_ph_blk ly3 S3 W3 (ms_mem ms3) md3 fp (n_b cx) (Z.of_nat (length (n_C cx))) HAR Hfin
                       ltac:(rewrite HAB; exact Hbin0)) as D; rewrite HFA in D; exact D|].
      split; [unfold NO_PH; clear - HF1; lia|].
      split; [pose proof (proj2 (proj2 (proj2 (hd_ph_place ly3 S3 W3 (ms_mem ms3) md3 fp HAR Hfin)))) as D;
              rewrite HFA in D; exact D|].
      split.
      { left. exists NX_CID, fp. split; [exact Hfin|]. intros a Ha.
        unfold in_zr, frame_rng. cbn [fst snd]. rewrite hd_fsb.
        unfold NO_PH, NX_PH_LEN, nF in *. rewrite HFA in *. lia. }
      split.
      { intros a Ha. split.
        - apply awr_byte_own_head. rewrite hd_fsb. unfold NO_PH, NX_PH_LEN, nF in *. rewrite HFA in *. lia.
        - rewrite Hspc. unfold NO_PH, NX_PH_LEN, NX_STK in *. lia. }
      split; [exact HRAd | intros _; exact HHULL]. }
  cbv beta. intros W4 c4 Hwle (ly2 & S2 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & HK4 & HQ4).
  pose proof HQ4 as (Hly2 & HS2 & _). subst ly2 S2.
  rewrite Hspc in HK4. rewrite Q1.
  apply (HN cx fp k2 ly3 S3 W4 (mkst regs4 (Z_to_bv 64 (pa_val A_TEXT + NP_hd_ra)) mem4 (seg_rom SEGS)) md4
    HB HJ4 HFR).
  exact (hd_land cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR HAB memc W4 mem4 Hh HRUN HK4
           R q lh regsc mdc ly3 S3 regs4 md4 HR HL HPc H4 H5 Hfdc Hfsc HJ4 HP4 HQ4).
Qed.
End c.
End b.
End a.

(* SK is explicit (a Theorem Labs lane ruling 21:57Z, as PcapSourceNextDefs.v): the closure's only global sink_head
   instance is the plain build's, so an inferred SK would make the stream facts vacuous. *)
Arguments pb_hdA {fx rc} SK {PI}.
Arguments hd_to_call {fx rc} SK {PI}.
