(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import MM_syscalls.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import SysStepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg AProto ABase AKit AKit2 RT_stubs F_ammap FsKit.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= solve_load_g.
Local Ltac solve_store ::= solve_store_g.

Section CANSEC1. Context {rc : runConstT}.
Definition AMMAPFNR : Z := 0x6d5c8.
Definition F_FIXNORES_RW_FLAGS : Z := 16434.       (* [comment removed for export] *)
End CANSEC1.
Notation FNR_STACK := 368 (only parsing).        (* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Definition fnr_cells (m : amem) : Prop :=
     rw_cells asegs m 0x98e18 [C8 (Z_to_bv 64 0x130920)]
  /\ rw_cells asegs m 0x130920 [C8 (Z_to_bv 64 4096)]
  /\ rw_cells asegs m 0x98e28 [C8 (Z_to_bv 64 0x1329a8); C8 (Z_to_bv 64 0x9e678); C8 (Z_to_bv 64 0xa0e78);
                               C8 (Z_to_bv 64 0xa1b68); C8 (Z_to_bv 64 0xa1b70); C8 (Z_to_bv 64 0xa1b60)]
  /\ rw_cells asegs m 0x132a38 [C8 (Z_to_bv 64 0)].

#[using="Type"] Lemma fnr_cells_frame : forall m m' W, fnr_cells m -> munch W m m' -> wmono asegs m m' ->
  Forall (fun iv => AIMG_HI <= fst iv) W -> fnr_cells m'.
Proof.
  intros m m' W (R1 & R2 & R3 & R4) MU WM HW. unfold AIMG_HI in HW.
  assert (D : forall A k, 0 <= k -> A + k <= 0x5f6000 -> disjoint_from W A k).
  { clear -HW. intros A k Hk HA. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion HW; subst. cbn in *. split; [lia| apply IH; assumption]. }
  unfold fnr_cells. repeat lazymatch goal with |- _ /\ _ => split end;
    (eapply rw_cells_transport; [eassumption | exact MU | exact WM | cbn; apply D; lia]).
Qed.

Definition fnr_post (RNG : footprint) (sp : word) (addr size lo : Z) (m : amem) (RNG' : footprint) (m' : amem) : Prop :=
     fp_le RNG RNG'
  /\ munch [(bv_unsigned sp - FNR_STACK, bv_unsigned sp); (addr, addr + size)]%Z m m' /\ wmono asegs m m'
  /\ mem_inv asegs m'
  /\ stk asegs m' lo (bv_unsigned sp)
  /\ rw_cells asegs m' addr [CB (Z.to_nat size) (repeat (Z_to_bv 8 0) (Z.to_nat size))]
  /\ rng RNG' addr size
  /\ fp_bw RNG'
  /\ fnr_cells m'.

#[using="Type"] Lemma fnr_spec : forall RNG {R} (K : Z -> itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (addr size lo : Z) (junk : list byte),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - FNR_STACK ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 addr -> a1 = Z_to_bv 64 size -> a2 = Z_to_bv 64 0 ->
  addr mod 4096 = 0 -> size mod 4096 = 0 -> 0 < size -> AIMG_HI <= addr -> addr + size <= 0x10007fff8000 ->
  fnr_cells m ->
  rw_cells asegs m addr [CB (Z.to_nat size) junk] ->                 (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG addr size ->
  (* [comment removed for export] *)
  (forall a RNG' ms', a <> addr -> 0 < a -> a + size <= ATOP -> implS asegs RNG' (K a) (epostF Q) ms') ->
  (forall RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      fnr_post RNG sp addr size lo m RNG' m' ->
      implS asegs RNG' (K addr) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (ebind (enode (NMmap addr size 3 F_FIXNORES_RW_FLAGS) (adec_mmap ATOP size 3)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AMMAPFNR) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros ST CEIL LO MI -> -> -> AAL SAL SPOS A0 AHI RC DST RIMG RSTK RTGT UNR KONT. unfold AIMG_HI in A0.
  pose proof RC as RC0. destruct RC0 as (GPG & PGSZ & GOT & MLIM).
  unfold AMMAPFNR, F_FIXNORES_RW_FLAGS in *. word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - FNR_STACK, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  eapply (implF_ebind _ _ _ _ _ _ _
            (fun a RNG' ms' => (a <> addr /\ 0 < a /\ a + size <= ATOP) \/ a = addr /\ exists m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
               fnr_post RNG sp addr size lo m RNG' m' /\
               ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom asegs))).
  2: { intros a RNG' ms' [(NE & P1 & P2)|[-> PO]]; [apply UNR; [exact NE | exact P1 | exact P2]|].
       destruct PO as (m' & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & PO & ->).
       eapply KONT. exact PO. }
  (* [comment removed for export] *)
  iprefix.
  Local Ltac2 Set LiaHints.tbl := fun () => "04N0>10667180602.7910873507702.941162083374.76 1164180523.94 11647286254.7111647286254.7411805467289.7111805467289.7311805467289.7411805467289.7511805467289.7611805467289.7711805467289.7912429510126.7413425838126.7714516788362.7914761575534.7314761575534.7514866570234.7715107956284.7915116433660.9515788225262.7915813913888.8015813913902.7816290529959.761772731779.77 1772731779.79 17776320428.7217778417576.9317976286208.2 1800609155.73 1800609155.94 1809810926.79 18689773242.7718890355993.7718893895214.7718900419239.7919391258279.7719870165642.7419879235054.7920163737475.7520163737475.9520438143011.8320447870595.7920447870595.8121811810457.792190890265.77 22102740889.7922232942.77   22389541692.7122927418606.792350913305.77 23715658734.7924018494190.7924179267756.7624179267758.782435347822.77 24638473347.7424638473347.9525071629079.9525077027338.7725240764910.7125240764910.7425645433846.7925878270243.9225878270253.7326431752068.6 27066288442.7627408782893.7527408782895.7727778003822.7327778003822.7527797263342.7627907155234.8128001526702.9528125558140.8028370640551.7528417259964.7329514832494.7329514832494.752993314286.71 2993314286.74 30023022247.7730231011258.7730603927662.7330603927662.753071671100.79 31378308326.6531929422315.7531940628442.6732377744366.7432631783278.7733680001082.7433680001082.7733875968138.7133875968138.7433962954137.7634122977177.7934285919648.7934285919662.763438046198.94 34417933740.7634417933741.7534430152252.7434924112163.7035082589626.7735205357699.7735205357699.9535900719086.7936106342346.7736107562391.8536113525291.9436115622447.7336590710439.7736637980185.7536654913774.7436654913774.7737609348206.7737827660420.6637845668334.7438178687114.8138214450030.7739238442350.7739571573379.7939571573379.8140089828523.9440091925676.7440150930599.7740457739452.7340527739801.7440608002030.7140608002030.7441272171651.7441272171651.9342085054489.7742115887662.7742236688921.7742488118638.7342488118638.7542501437472.9542503534630.7242505299482.6742511411968.8042511604512.8142511604641.8142817538363.8242882700782.7643059266230.6343175993206.9443985854248.9343987951407.7343988483203.7143988483203.934472014211.76 4472014211.77 44950045500.774497338734.77 45221239098.7445352467587.7945352467587.8145415010670.7345415010670.7545848756903.7146356275438.7446356275438.7746468661564.7446895624871.7946923015598.9546998232647.6847230136046.7947296502915.7647296502915.7849288693539.8349562070382.7749649769127.7449710714478.7749734724014.9549750950894.7449903997356.8349935451210.9550131542183.7550645511577.7950703419246.7750975666620.755098644739.95 51124399684.705120733337.76 51215735434.7651612993875.6 51678667180.7451680764331.9451711223320.8052105090727.735289276057.79 53424079911.9553540834542.7953667699702.9453767577772.7253769674920.9353904676268.8354243526019.7354243526019.9454367113454.795575378976.80 5575378990.78 55768096166.6856064834414.7356064834414.7556084093934.76563227834.73  563227834.75  56759370246.7 56779838332.6956986461756.7457269508355.7757269508355.8057697684362.7457697684362.7757745675194.7357745675194.7557897936679.7758762852128.8058762852142.7858776000537.7759314873579.7 59314873579.8 59758911548.795998835466.77 60084855288.8360274535852.8360511482531.816066363658.73 6066363658.75 60858483367.7461170136174.7761254491452.7661439603310.7361439603310.756165337146.79 61988516505.7963014048956.7563235321891.9263235321901.7063305555623.7363341493050.7964026414714.9564259584380.7764772824451.7564772824451.9564896830119.7964997134979.7464997134979.9465104334021.8165104450989.5 65299792814.9565666169454.7765769723580.7765845987594.7765896949806.7766330498732.7666330498734.7866554270958.7966571591084.8366794420697.7767284288444.7767471419575.8267696566282.7367696566282.756783195886.79 68393266841.7768501319406.7468501319406.777125526410.79 730490250.79  7373603310.76 7486304935.74 7600465283.77 7600465283.79 8405736896.95 8583720762.71 8583720762.74 8772567833.75 9099241916.77 9191764522.94 9956545262.74 9956545262.77 00000500600:00>00G00P00Q00R00S00T00U00V00W00`00i01;01D01M01R01V01Z01c01g01k01l01m01n02202602<02=02>02G02L02M02V02W02X02j03303403503B03C03D03E03F03G03P03T03]03^03g04004404804A04B04C04D04V04_04h04i04m05105605;05?05C05L05U05^05b05k05l05m06106:06C06L06U06V06[06d06m07107207?07L07U07^07c07h08:08L08M08N08R08V08W08[08_08c08g08l08m08n09709I09O09S09W09X09Y09b09k0:40:80:A0:B0:K0:T0:U0:V0:Z0:^0:_0:c0:d0:m0;60;70;80;90;B0;C0;L0;U0;\0;i0<60<C0<J0<W0<X0<a0<e0<f0<j0<n0<o0=00=10=20=60=?0=D0=E0=F0=O0=X0=Y0=b0=k0=o0>00>90>:0>C0>D0>E0>R0>[0>\0>e0>n0?70?;0?M0?N0?O0?X0?\0?]0?^0?_0@10@60@:0@>0@?0@@0@A0@B0@K0@L0@P0@T0@X0@Y0@Z0@c0@g0@k0@o0A80AA0AJ0AO0AT0Ad0Ae0Ai0Aj0Ak0B=0BO0BT0BY0BZ0B^0Bb0Bc0C20CD0CH0CZ0C[0C_0Cc0D50DG0DH0DQ0DU0D^0Dg0Dl0Dm0E10E50E90E:0E?0ED0EH0EI0EJ0EK0EL0EM0EZ0Eg0F00F90F=0FO0FX0F\0F`0Fi0Fm0Fn0G20G70GI0G[0Gd0Ge0Gn0H70HI0H[0Hd0He0Hf0Hg0Hh0Hm0I20I30I70I;0ID0IMS3SPRSS2LOS2LOS4CEIL2LOS4CEIL2LOSSSSSSSS4CEIL2LOS4CEIL2LOS4CEIL2LO4SPOS3AHIS4CEIL2LOS4CEIL2LOS3SPRS2HBS2HBS4CEIL2LOS2LOS2LOSSSS2LOS2LOS4SPOSSSS4CEIL2LOS3SPRSS4CEIL2LOSSS4CEIL2LO4SPOS3AHIS4CEIL2LOSSS4CEIL2LO3AHISSSSSS4CEIL2LOS2HBS4CEIL2LOSS4CEIL2LOS4CEIL2LOS2LOS2LOS4CEIL2LOSSSS4CEIL2LO4SPOS3AHIS4CEIL2LOS4CEIL2LOSS2LOS2LOS3SALS3SPRS2LOS2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS2LOS4CEIL2LOSSS2HBS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOSS3SPRS4CEIL2LOS4CEIL2LOS2HBSS4SPOS2A03AHIS4SPOS2A03AHIS4CEIL2LOS4CEIL2LOS3SPRS3SPRS4CEIL2LO4SPOS3AHIS4CEIL2LO4SPOS3AHISSS2LOS2LOSS2LOS2LOS2HBS2LOS3SPRSSS4CEIL2LOS4CEIL2LO4SPOS3AHIS2A01HS2LOS2LOSSS4CEIL2LOS4CEIL2LOS4CEIL2LOS2LOS4CEIL2LOSS4CEIL2LOS4CEIL2LOSSS2LOS2LOSS2HBSS4CEIL2LOS4CEIL2LOSSSS4CEIL2LOSS4CEIL2LOS4CEIL2LOS2A02K1S4SPOS2A03AHIS4SPOS2A03AHIS4SPOS2A03AHIS2A02K1S4SPOS2A03AHISS4CEIL2LOS2LOSS2LOS2LOSSSSS2HBS4CEIL2LOS3SPRSSS4CEIL2LOS4CEIL2LOSS4CEIL2LOS4CEIL2LOS2HBSS4CEIL2LOSS4CEIL2LOSSS4CEIL2LO3AHIS4CEIL2LOSS4CEIL2LOS4CEIL2LOS4CEIL2LOS2A0S4CEIL2LO4SPOS3AHISSS4CEIL2LOS2HBSSSS4CEIL2LO4SPOS3AHIS3AALS2LOS2LOSSSSS4CEIL2LOSS2LOS2LOS2A0SSS4CEIL2LOS2LOS2LOS2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS3SPRS3SPRS4SPOS3AM23AM31HSS2HBSSS4CEIL2LO4SPOS3AHIS4CEIL2LO4SPOS3AHIS3SPRS3SPRSS2LOS2LOSS4SPOS3AM32LT1HS4SPOS3AM32K11H2K2S2HBS4CEIL2LO4SPOS3AHIFS2A0S2LOS4CEIL2LO4SPOS3AHIS4CEIL2LO4SPOS3AHISS4CEIL2LOS2HBS4CEIL2LOS4CEIL2LOS3SPRSS2HBS2LOS2LOSS3SPRS3SPRS2HBSSSSSS4SPOS2A03AHIS4SPOS2A03AHIS4CEIL2LOS4CEIL2LOS2HBS4CEIL2LO4SPOS3AHIS4CEIL2LOS2LOS2LOS4CEIL2LOS2A0SS2HBS3AHIS4CEIL2LO4SPOS3AHIS4CEIL2LO4SPOS3AHIS4CEIL2LOSS4CEIL2LOS4CEIL2LOS4CEIL2LO4SPOS3AHIS4CEIL2LO4SPOS3AHIS4CEIL2LOSSSFS3SPRS3SPRSS2HBS2LOS4CEIL2LOS4CEIL2LO".
carve_frame 48%nat ST.
  do 6 step.                                                   (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  step. step. if_lit.                                          (* [comment removed for export] *)
  zstep. zstep. step. if_lit.                                  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.                                  (* [comment removed for export] *)
  setreg 8 (Z_to_bv 64 size) ltac:(rewrite land_align4096 by lia; f_equal; clear -SAL SPOS AHI A0; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  step. if_lit.                                                (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  setreg 18 (Z_to_bv 64 addr) ltac:(rewrite Z.land_comm, land_align4096 by lia; f_equal; clear -AAL A0 AHI SPOS; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  step. step. step. step. step. step.                          (* [comment removed for export] *)
  (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  carve_frame 48%nat ST.
  do 5 step.                                                   (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  carve_frame 272%nat ST.
  do 8 step.                                                   (* [comment removed for export] *)
  step. step. step. if_lit.                                    (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  do 9 step.                                                   (* [comment removed for export] *)
  release_frame FR1 ST (bv_unsigned sp + -96).
  step. setreg 13 (Z_to_bv 64 16434) ltac:(vm_compute; reflexivity).   (* [comment removed for export] *)
  step. step. step. step. step.                                (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  (* [comment removed for export] *)
  icallk rt_mmap_stubP.
  intros a RNG' ms' (rsp & HF & Hdec & ->).
  destruct (adec_mmap_rw_Some _ _ _ Hdec) as (ci & -> & AM1 & AM2 & AM3).
  pose proof (page_round_up_mult size SAL ltac:(clear -SPOS; lia)) as PRU. unfold mmap_len in *. rewrite PRU in AM3. rewrite PRU.
  pose proof (fstepA_mmap_grant addr size 16434 _ RNG RNG' (fstepS_fstepA _ _ _ _ HF)) as GR. cbn [eff_ret] in GR.
  rewrite (unsigned_lit a) in GR by (clear -AM2 AM3 SPOS; lia). rewrite (unsigned_lit size) in GR by (clear -SPOS AHI A0; lia).
  rewrite PRU in GR. specialize (GR ltac:(unfold page_size; exact AM1)).
  pose proof HF as HF0. fstepS_transport HF.
  destruct (Z.eq_dec a addr) as [->|NE]. 2: { apply evtF_done. left. split; [exact NE|]. split; [exact AM2| atop_facts; exact AM3]. }
  unfold rt_regs. cbn [eff_ret]. rewrite eff_mem_zeros.
  replace (ret_pc (Z_to_bv 64 0x65130)) with (Z_to_bv 64 0x65130 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  apply (munch_weaken _ [(bv_unsigned sp - FNR_STACK, bv_unsigned sp); (addr, addr + size)]%Z) in MU.
  2: { unfold sub_fp. cbn [outside]. clear. intros x Hx. tauto. }
  sys_mem_zeros.
  (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  step. step. step. if_cases K1; zify_cond K1. 2: { exfalso. clear -K1 AM3 SPOS A0. lia. }   (* [comment removed for export] *)
  zstep. step.                                                 (* [comment removed for export] *)
  setreg 10 (Z_to_bv 64 0) ltac:(f_equal; destruct (Z.ltb_spec 18446744073709547520 addr) as [LT|GE]; [exfalso; clear -AM3 SPOS LT; lia| reflexivity]).
  step.                                                        (* [comment removed for export] *)
  step. step. step. step. step. step.                          (* [comment removed for export] *)
  lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -96) _, STK : stk asegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp + -48) end.
  (* [comment removed for export] *)
  step. step. step. step. step.                                (* [comment removed for export] *)
  step. step. step. if_cases K2; zify_cond K2. 2: { exfalso. clear -K2 AM3 SPOS A0. lia. }
  zstep. step.
  setreg 10 (Z_to_bv 64 0) ltac:(f_equal; destruct (Z.ltb_spec 18446744073709547520 addr) as [LT|GE]; [exfalso; clear -AM3 SPOS LT; lia| reflexivity]).
  step. step. if_lit.                                          (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  step. step. step. step. if_lit. step.                        (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  step. step. step. step. step. step. step.                    (* [comment removed for export] *)
  lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -48) _, STK : stk asegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
  apply evtF_done. right. split; [reflexivity|].
  do 15 eexists. split. 2: reflexivity.
  unfold fnr_post. destruct HF0 as [[FPLE _] [_ BW]].
  split; [exact FPLE|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [exact ZNEW|]. split; [exact GR|]. split; [exact BW|].
  unfold fnr_cells. repeat (split; [assumption|]). assumption.
  Unshelve. all: apply ref_ro_addr_false; right; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC2.
