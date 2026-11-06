(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim Monad Stdio Driver.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import Shadow ITreeA.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg F_syscalls StdioFiles Stdio_kit MonadF F_memset AExit F_stdio_exit.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StrwF SysStepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Import ITree.Exc.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation mem := (word -> option byte).

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition SHOFF : Z := 0x7fff8000.
Definition shd (a : Z) : Z := SHOFF + Z.shiftr a 3.
Definition shn (l : Z) : Z := Z.shiftr l 3.

(* [comment removed for export] *)
End CANSEC1.
Ltac sort_lits :=
  repeat (match goal with H : rw_cells asegs _ (Zpos ?p) _ |- _ =>
            tryif (match goal with H' : rw_cells asegs _ (Zpos ?p') _ |- _ =>
                     lazymatch eval vm_compute in (Z.ltb (Zpos p') (Zpos p)) with true => idtac | false => fail end end)
            then fail
            else (move H at bottom; lazymatch type of H with ?T => change T with (sf_hide T) in H end)
          end); sf_unhide.
Ltac hstep := sort_lits; zstep; fix_lit_store.
Ltac astep := hstep; try (first [if_true | if_false]).
Ltac at_pc p := lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => constr_eq q p end.
Ltac steps_to p := repeat (tryif at_pc p then fail else astep).

Section CANSEC2. Context {rc : runConstT}.
#[using="Type"] Lemma unsigned_lit8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. Local Ltac2 Set LiaHints.tbl := fun () => "0010<9536388762.3000003S1H".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mdtor_rt (m : mem) : Prop :=
     rw_cells asegs m 0x98e18 [C8 (Z_to_bv 64 0x130920)]                                        (* [comment removed for export] *)
  /\ rw_cells asegs m 0x98e28 [C8 (Z_to_bv 64 0x1329a8); C8 (Z_to_bv 64 0x9e678); C8 (Z_to_bv 64 0xa0e78);
                                C8 (Z_to_bv 64 0xa1b68); C8 (Z_to_bv 64 0xa1b70); C8 (Z_to_bv 64 0xa1b60)]  (* [comment removed for export] *)
  /\ rw_cells asegs m 0x98e58 [C8 (Z_to_bv 64 0x9acc0)]                                        (* [comment removed for export] *)
  /\ rw_cells asegs m 0x9acb8 [C8 (Z_to_bv 64 0x92164); C8 (Z_to_bv 64 0x92568)]              (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa0e78 [C8 (Z_to_bv 64 0x7fff8000)]                                      (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa1b58 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]                              (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa06dc [C1 (Z_to_bv 8 1)]                                                (* [comment removed for export] *)
  /\ rw_cells asegs m 0x132a20 [C8 (Z_to_bv 64 0xffffffffffffffff)]                                         (* [comment removed for export] *)
  /\ rw_cells asegs m 0x9e690 [C4 (Z_to_bv 64 1)].                                              (* [comment removed for export] *)

(* [comment removed for export] *)
Definition rt_clear (iv : Z * Z) : Prop :=
  let (lo, hi) := iv in
  lo <= hi /\
  (hi <= 0x98e18 \/ (0x98e60 <= lo /\ hi <= 0x9acb8) \/ (0x9acc8 <= lo /\ hi <= 0x9e690) \/ (0x9e694 <= lo /\ hi <= 0xa06dc)
   \/ (0xa06dd <= lo /\ hi <= 0xa0e78) \/ (0xa0e80 <= lo /\ hi <= 0xa1b58) \/ (0xa1b5a <= lo /\ hi <= 0x132a20) \/ 0x132a28 <= lo).

#[using="Type"] Lemma mdtor_rt_frame : forall m m' W,
  mdtor_rt m -> munch W m m' -> wmono asegs m m' ->
  Forall rt_clear W -> mdtor_rt m'.
Proof.
  intros m m' W PC MU WM HW.
  assert (D : forall A n, 0 <= n ->
             ((0x98e18 <= A /\ A + n <= 0x98e60) \/ (0x9acb8 <= A /\ A + n <= 0x9acc8) \/ (0x9e690 <= A /\ A + n <= 0x9e694)
              \/ (0xa06dc <= A /\ A + n <= 0xa06dd) \/ (0xa0e78 <= A /\ A + n <= 0xa0e80) \/ (0xa1b58 <= A /\ A + n <= 0xa1b5a)
              \/ (0x132a20 <= A /\ A + n <= 0x132a28)) -> disjoint_from W A n).
  { intros A n Hn HA. clear MU. induction HW as [|[lo hi] W H1 H2 IH]; cbn in *; [exact I|]. Local Ltac2 Set LiaHints.tbl := fun () => "00;0>19593506997.1733230757493.1733666907028.1733770765749.1738189781429.1744970843957.1744995353781.1757439793845.1768060973103.1768595141598.159972703541.17 00000100200300400500600700800900@00ASSSSSSSSSS2H12HAS".
split; [lia| exact IH]. }
  unfold mdtor_rt in *.
  destruct PC as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
  repeat match goal with |- _ /\ _ => split end; (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply D; cbn; lia]).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition poison_low_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (sb sl lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (sb, sb + sl)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' sb [CB (Z.to_nat sl) (repeat (Z_to_bv 8 0) (Z.to_nat sl))].

#[using="Type"] Lemma poison_low_spec : forall RNG (sb sl : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (addr size lo : Z) (junk : list byte),
  stk asegs m lo (bv_unsigned sp) -> KHIGH <= lo -> lo <= bv_unsigned sp - 64 ->
  mem_inv asegs m ->
  mdtor_rt m ->
  a0 = Z_to_bv 64 addr -> a1 = Z_to_bv 64 size -> a2 = Z_to_bv 64 0 ->
  addr mod 8 = 0 -> size mod 8 = 0 -> 0 < size -> 0x10000 <= addr -> addr + size <= 0x5f6000 -> shn size < 0x10000 ->
  sb = shd addr -> sl = shn size ->
  rw_cells asegs m sb [CB (Z.to_nat sl) junk] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG sb sl ->
  evtF asegs RNG (poison_low_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc sb sl lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x52f70) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros ST KH LO MI RT -> -> -> AL SL SZ LOW HIE SMALL -> -> DST RIMG RSTK RSH.
  unfold KHIGH in KH. pose proof RT as RT'. destruct RT' as (PGC & GOT & GOT80 & REAL & SHB & INI & CANP & THR & RGL).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (shd addr, shd addr + shn size)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (SHR : 0x7fffa000 <= shd addr /\ shd addr + shn size <= 0x800cd000 /\ 0 < shn size).
  { unfold shd, shn, SHOFF. Local Ltac2 Set LiaHints.tbl := fun () => "02H0>100583406.77  11647286254.7711801259171.9311912744615.7612367362435.7612367362435.8213021749692.761340665966.76 14684412918.8114869235822.761527479463.74 15629760750.7717000728814.7417646078182.6717776320430.8217776320431.7519049469500.7619618399904.872027029998.76 20313996398.7621918414723.7621918414723.8323893911790.7424630998586.7424982578106.7124982578737.6925071629079.7425071629079.7625071629079.7725240764910.7725259836654.7425314760359.7625878270254.8225878270255.7526074863037.7226082619953.8027453056622.7627981583342.7728913119922.8129514832494.7629784417117.6929784418006.7129784612193.6329786514270.7329794353372.8730410309102.7630603927662.7631081687356.7732377744366.7632651489978.7633039531175.7733486665994.7733680001082.7734056952330.7734255743086.7634874897390.7735010564462.7635499796014.7336115622446.7636115622446.8236423573305.9536993589379.7736993589379.8337107179452.7637774863470.7637845668334.7639219183342.743945979267.76 3945979267.82 41362836762.6341809558659.7441809558659.8142309226734.7442488118638.7642501437472.8742501437473.8642503534633.7942511604512.7042847154798.7643060403331.7743060403331.8343061415849.654359095406.76 43987951406.7643987951406.824413803118.76 44483185911.9444750652170.764495156590.76 45221239098.7646356275438.7746388204398.7647219577582.7747407242478.7648757815150.7749343888933.9550693720814.7751106262638.7651481786499.7651481786499.8352076332701.8053767577775.7553767577775.8153827994990.7655737922668.9355748147788.7455750620234.7455810868206.7656064834414.7656066145674.7656228262055.76563227834.76  5638167690.74 5652583082.93 57733900014.7757745675194.7657839090926.7458388211694.7659308628433.7059308629336.7259308632823.7459310725459.7359391397898.7459445487498.7659588178610.8160025031335.7760366604398.7661674577390.7661917199023.7561917199023.8162233662062.7663235321900.7363235321900.8063694018620.7764635471598.7765098632080.7865752782446.7766761942666.7667503714926.7667800801447.7668010266983.7368501319406.7768714883566.766896978414.76 7010956092.74 8014158190.74 8492783342.74 8583720762.77 9053231598.77 9155751918.77 9333008750.76 985337532.76  00000700>00I00J00K00L00P00W00X00_00`00g00n00o01301701;01<01C01J01K01L01S01X01Y01Z01[01\01]01d01k01l02002402@02L02S02Z02[02b02c02d02e02f02g02n03503903@03E03F03Q03V03a03h03o04604704;04?04C04D04E04I04P04W04^04_04`05205305405;05B05J05R05^05j06106206306706>06B06F06M06U06`06g06l07307:07A07H07O07P07W07^07_07`07a07e07i08008;08F08Q08X08_08j08k09009509:09A09F09M09T09_09g0:10:60:A0:L0:M0:N0:U0:\0:`0:d0:k0:o0;30;70;>0;J0;Q0;\0;c0;d0<60<=0<D0<K0<O0<V0<]0<b0<i0=00=70=;S2KH2LOS2KH2LOS2KH2LO3SHRSSSS2HBS2KH2LOSS2KH2LOSS2KH2LOS2KH2LOSS2LOS2LOS2HBFS2KH2LOS2KH2LOSSS2KH2LOS3RSPSSSSSS2KH2LOS2KH2LOSS2LOS2LOS2SZ3LOW3HIES2SZ3LOW3HIES2KH2LOS2KH2LOSS2KH2LOSSSSSS2KH2LOS2KH2LOS2HBS2KH2LOS3RSPSS2KH2LO3SHRS3RSPS2KH2LO3SHRS2KH2LOS2KH2LOS2KH2LOSS2LOS2LOS2LOSSS2HBS2KH2LOS2KH2LOS2KH2LOSSS2AL2SL2SZ3LOW3HIESSS2KH2LOS2KH2LOS3LOW2K2S3LOW2K2S2SZ3LOW3HIES2SZ3LOW3HIES2KH2LOSSS2LOS2KH2LOS2LOS2LOS2KH2LOS2KH3SHRS2KH2LO3SHRS2KH2LOS3RSPS2KH2LOS2KH2LOS2KH2LOS2KH2LOS2KH2LOSS2KH2LOS2KH2LOSSFS2LOS2LOS2KH2LOS5SMALL3SHRS5SMALL3SHRS5SMALL3SHRS2KH2LOS2KH2LOS2KH2LO3SHRSS3RSPS3SHRS3SHRS2KH2LOS3RSPS2KH2LOS2KH2LOS2SZ3HIE2K2S3HIE2K9S5SMALL2KTS3K10S2KH2LO3SHRS2KH2LO3SHRSSS2KH2LOS2KH2LOS2LOS2LOS2KH2LOS2LOS2LOS2HBS2KH2LOS2SZ3LOW3HIES2KH2LOS2KH2LO3SHRS2KH2LOSS2AL2SL2SZ3LOW3HIES2KH2LOS2KH2LOS2KH2LOS2HBS2KH2LOS2KH2LOS3RSPS2KH2LOS2KH2LOS2KH2LOS2HB".
rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  carve_frame 64%nat ST.
  do 8 hstep.                                          (* [comment removed for export] *)
  hstep. if_true.                                      (* [comment removed for export] *)
  zstep. hstep. if_cases K1; zify_cond K1.              (* [comment removed for export] *)
  { exfalso. apply K1. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. exact AL. }
  do 3 hstep.                                          (* [comment removed for export] *)
  do 4 zstep.                                          (* [comment removed for export] *)
  match goal with |- context [Z.land ?x 2147450879] => let v := eval vm_compute in (Z.land x 2147450879) in change (Z.land x 2147450879) with v end.
  hstep. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }   (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. hstep. if_cases K8; zify_cond K8.
  { exfalso. apply K8. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. exact SL. }
  do 2 zstep.                                          (* [comment removed for export] *)
  hstep. if_cases K9; zify_cond K9. 2:{ exfalso. lia. }   (* [comment removed for export] *)
  (* [comment removed for export] *)
  do 3 hstep.                                          (* [comment removed for export] *)
  hstep. if_cases K10; zify_cond K10; [exfalso; lia|]. (* [comment removed for export] *)
  do 5 zstep.                                          (* [comment removed for export] *)
  assert (E1 : Z.land (Z.shiftr (addr + size + -8) 3 + 1) 18446744073709551615 - Z.shiftr addr 3 = shn size).
  { unfold shn. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. change 18446744073709551615 with (Z.ones 64).
    rewrite Z.land_ones by lia. change (2 ^ 64) with 18446744073709551616. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  rewrite E1. clear E1. change (2147450880 + Z.shiftr addr 3) with (shd addr).
  hstep. if_false.                                     (* [comment removed for export] *)
  do 3 hstep.                                          (* [comment removed for export] *)
  hstep. if_cases KT; zify_cond KT.                    (* [comment removed for export] *)
  2:{ exfalso. lia. }
  do 3 hstep. do 8 hstep.                              (* [comment removed for export] *)
  hstep.                                               (* [comment removed for export] *)
  eapply evtF_mono.
  { eapply memset_spec; [ rewrite !unsigned_lit by lia; exact DST | exact MI | rewrite !unsigned_lit by lia; exact RSH ]. }
  intros ms' PO. unfold memset_post in PO. unfold poison_low_post. destruct_exs PO.
  destruct PO as (-> & MU2 & WM2 & MI2 & DST2).
  rewrite !unsigned_lit in MU2, DST2 by lia. change (0 mod 256) with 0 in DST2.
  do 16 eexists. split; [reflexivity|].
  split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. intros xq Hxq. cbn in Hxq |- *. tauto. }
  split. { eapply wmono_trans; [exact WM| exact WM2]. }
  split. { exact MI2. }
  split. 2: exact DST2.
  pose proof (rw_cells_transport asegs _ _ _ _ _ FR MU2 WM2 ltac:(cbn [disjoint_from cells_size csize]; lia)) as FR'.
  pose proof (stk_transport_disjoint asegs _ _ _ _ _ ST MU2 WM2 ltac:(cbn [disjoint_from]; lia)) as ST'.
  eapply stk_release in FR'; [| exact ST' | lia]. cbn [cells_size csize Nat.add] in FR'.
  match type of FR' with stk _ _ _ ?hi => replace hi with (bv_unsigned sp) in FR' by lia end. exact FR'.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition unreg_one_post (spv d sb sl : Z) (gp tp s5 s6 s8 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR (Z_to_bv 64 0x3f284) (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 (Z_to_bv 64 0x1329a8) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 2) (Z_to_bv 64 0x1b21d) (Z_to_bv 64 d) s5 s6 (Z_to_bv 64 0x9acc0) s8 (Z_to_bv 64 0x9e678)
                  (Z_to_bv 64 0xa0e78) s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x3f284) fc None m' (seg_rom asegs)
    /\ munch [(sb, sb + sl)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' sb [CB (Z.to_nat sl) (repeat (Z_to_bv 8 0) (Z.to_nat sl))].

#[using="Type"] Lemma unreg_one_spec : forall RNG (sb sl : Z) (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s8 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem) (spv d beg swr : Z) (gsz gnm gmd gdy glc godr : word) (junk : list byte),
  mem_inv asegs m -> mdtor_rt m ->
  rw_cells asegs m d [C8 (Z_to_bv 64 beg); C8 gsz; C8 (Z_to_bv 64 swr); C8 gnm; C8 gmd; C8 gdy; C8 glc; C8 godr] ->
  rw_cells asegs m (d + 16) [C1 (Z_to_bv 8 swr)] ->
  beg mod 8 = 0 -> swr mod 8 = 0 -> 0 < swr < 256 -> 0x10000 <= beg -> beg + swr <= 0x5f6000 ->
  0x10000 <= d -> d + 64 <= 0x5f6000 -> 0 <= spv < 2^64 ->
  sb = shd beg -> sl = shn swr ->
  rw_cells asegs m sb [CB (Z.to_nat sl) junk] ->
  rng_aimg RNG -> rng RNG sb sl ->
  evtF asegs RNG (unreg_one_post spv d sb sl gp tp s5 s6 s8 s11 F fc m)
    (MS (mkR ra (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 (Z_to_bv 64 0x1329a8) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 2) (Z_to_bv 64 0x1b21d) (Z_to_bv 64 d) s5 s6 (Z_to_bv 64 0x9acc0) s8 (Z_to_bv 64 0x9e678)
             (Z_to_bv 64 0xa0e78) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3f29c) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros MI RT D DB AL SL SWR LOW HIE DLO DHI SPV -> -> DST RIMG RSH.
  pose proof RT as RT'. destruct RT' as (PGC & GOT & GOT80 & REAL & SHB & INI & CANP & THR & RGL).
  pose proof (munch_refl [(shd beg, shd beg + shn swr)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (SHR : 0x7fffa000 <= shd beg /\ shd beg + shn swr <= 0x800cd000 /\ 0 < shn swr < 32).
  { unfold shd, shn, SHOFF. Local Ltac2 Set LiaHints.tbl := fun () => "00\0>10009457963.7710009457963.8014684412918.7819620497065.8024115025141.8024982578487.6824982578614.6926082619952.7728913119920.8029001722024.7629001722024.7929071941542.8229601281241.6829784416347.6829784416474.6929784612193.6529786758908.6930422568588.7030424711306.7030426549930.8933161241475.7834303938864.8935499809676.6936350900204.6941209397009.7944170104438.7248107158204.8948109515932.7051563130523.8152076332688.7452076332702.7653510313876.7753817748470.7555047472860.7859308628433.6759308632823.7059588178608.8059702520969.6560996812196.8163674995624.7563677092781.8263683735724.6764713536689.7664713536689.7900000100200300400500600700D00E00F00G00H00M00N00O00P00Q00V00[00`00a00b00c01601701801=01B01C01D01E01F01G01P01\01d01e02802A02I02Q02^02g030SSSFFSSS3SWR3LOW3HIESFFFS3SWRSSSSS3SHRS3SHRS3SHRFSSS2AL2SL3SWR3LOW3HIESSS3SHRS3SHRFFFSSS3DLO3DHIS3SWR3HIE2K2S3SHR2KTSS2AL2SL3SWR3LOW3HIES3DLO3DHIS3LOW2K2S3LOW2K2S3SWR3LOW3HIES3DLO3DHIS3DLO3DHI".
rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  (* [comment removed for export] *)
  do 7 hstep.
  hstep. if_false.                                     (* [comment removed for export] *)
  hstep.                                               (* [comment removed for export] *)
  replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (vm_compute; reflexivity).
  hstep. if_true.                                      (* [comment removed for export] *)
  hstep. if_false.                                     (* [comment removed for export] *)
  (* [comment removed for export] *)
  do 2 hstep. do 4 zstep.
  match goal with |- context [Z.land ?x 2147450879] => let v := eval vm_compute in (Z.land x 2147450879) in change (Z.land x 2147450879) with v end.
  hstep. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }   (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. hstep. if_cases K3; zify_cond K3.
  { exfalso. apply K3. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. exact AL. }
  hstep. zstep. rewrite (unsigned_lit8 swr) by lia. hstep. if_cases K4; zify_cond K4.
  { exfalso. apply K4. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. exact SL. }
  (* [comment removed for export] *)
  do 6 hstep. hstep. if_false.
  (* [comment removed for export] *)
  do 3 hstep. do 5 zstep. hstep. do 3 zstep.
  assert (E1 : Z.land (2147450880 + Z.shiftr (beg + swr + -8) 3 + 1) 18446744073709551615 - Z.land (2147450880 + Z.shiftr beg 3) 18446744073709551615
               = shn swr).
  { unfold shn. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. change 18446744073709551615 with (Z.ones 64).
    rewrite !Z.land_ones by lia. change (2 ^ 64) with 18446744073709551616. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  rewrite E1. clear E1. change (2147450880 + Z.shiftr beg 3) with (shd beg).
  hstep. if_cases KT; zify_cond KT. 2:{ exfalso. lia. }  (* [comment removed for export] *)
  do 3 hstep.                                          (* [comment removed for export] *)
  eapply evtF_mono.
  { eapply memset_spec; [ rewrite !unsigned_lit by lia; exact DST | exact MI | rewrite !unsigned_lit by lia; exact RSH ]. }
  intros ms' PO. unfold memset_post in PO. unfold unreg_one_post. destruct_exs PO.
  destruct PO as (-> & MU2 & WM2 & MI2 & DST2).
  rewrite !unsigned_lit in MU2, DST2 by lia. change (0 mod 256) with 0 in DST2.
  cbn [ret_pc reg_get].
  replace (ret_pc (Z_to_bv 64 0x3f284)) with (Z_to_bv 64 0x3f284 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  do 17 eexists. split; [reflexivity|].
  split. { eapply munch_trans; [exact MU|]. exact MU2. }
  split. { eapply wmono_trans; [exact WM| exact WM2]. }
  split. { exact MI2. }
  exact DST2.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gdesc (m : mem) (d beg sz swr nm md odr : Z) : Prop :=
     rw_cells asegs m d [C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 sz); C8 (Z_to_bv 64 swr); C8 (Z_to_bv 64 nm); C8 (Z_to_bv 64 md);
                         C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 odr)]
  /\ rw_cells asegs m (d + 16) [C1 (Z_to_bv 8 swr)].

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AGLOBALS : list (Z * Z * Z * Z * Z) := [
  (0x20d40, 32, 64, 0x15811, 0x20dc0);
  (0x20d80, 32, 64, 0x15ec1, 0x20dc0)]%Z.
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint gdescs (m : mem) (d : Z) (G : list (Z * Z * Z * Z * Z)) : Prop :=
  match G with
  | [] => True
  | (b, sz, swr, nm, md) :: G' => gdesc m d b sz swr nm md (2^64 - 1) /\ gdescs m (d + 64) G'
  end.

(* [comment removed for export] *)
Fixpoint gsorted (lo hi : Z) (G : list (Z * Z * Z * Z * Z)) : Prop :=
  match G with
  | [] => True
  | (b, sz, swr, nm, md) :: G' =>
      lo <= shd b /\ shd b + shn swr <= hi /\ b mod 8 = 0 /\ swr mod 8 = 0 /\ 0 < swr < 256 /\ 0x10000 <= b /\ b + swr <= 0x5f6000
      /\ gsorted (shd b + shn swr) hi G'
  end.

(* [comment removed for export] *)
Fixpoint gshads (m : mem) (G : list (Z * Z * Z * Z * Z)) : Prop :=
  match G with
  | [] => True
  | (b, sz, swr, nm, md) :: G' => (exists j, rw_cells asegs m (shd b) [CB (Z.to_nat (shn swr)) j]) /\ gshads m G'
  end.

Fixpoint gsortedb (lo hi : Z) (G : list (Z * Z * Z * Z * Z)) : bool :=
  match G with
  | [] => true
  | (b, sz, swr, nm, md) :: G' =>
      (lo <=? shd b) && (shd b + shn swr <=? hi) && (b mod 8 =? 0) && (swr mod 8 =? 0) && (0 <? swr) && (swr <? 256)
      && (0x10000 <=? b) && (b + swr <=? 0x5f6000) && gsortedb (shd b + shn swr) hi G'
  end.

#[using="Type"] Lemma gsortedb_ok : forall G lo hi, gsortedb lo hi G = true -> gsorted lo hi G.
Proof.
  induction G as [|[[[[b sz] swr] nm] md] G IH]; intros lo hi H; cbn [gsortedb gsorted] in *; [exact I|].
  repeat rewrite andb_true_iff in H. destruct H as [[[[[[[[H1 H2] H3] H4] H5] H6] H7] H8] H9].
  apply Z.leb_le in H1, H2, H7, H8. apply Z.eqb_eq in H3, H4. apply Z.ltb_lt in H5, H6.
  repeat split; try assumption; try lia. apply IH. exact H9.
Qed.

#[using="Type"] Lemma AGLOBALS_sorted : gsorted 0x7fffc1a8 0x7fffc1b8 AGLOBALS.
Proof. apply gsortedb_ok. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma AGLOBALS_length : Z.of_nat (length AGLOBALS) = 2.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma cb_sub : forall m a (k : nat) j a' n', rw_cells asegs m a [CB k j] -> a <= a' -> 0 <= n' -> a' + n' <= a + Z.of_nat k ->
  exists j', rw_cells asegs m a' [CB (Z.to_nat n') j'].
Proof.
  intros m a k j a' n' [[WF [A0 [AL BY]]] [W0 [W1 W]]] H1 H2 H3.
  cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize] in *. destruct WF as [LJ _]. rewrite app_nil_r in *. rewrite Nat.add_0_r in *.
  exists (firstn (Z.to_nat n') (skipn (Z.to_nat (a' - a)) j)).
  assert (LEN : length (firstn (Z.to_nat n') (skipn (Z.to_nat (a' - a)) j)) = Z.to_nat n').
  { rewrite length_firstn, length_skipn. Local Ltac2 Set LiaHints.tbl := fun () => "0070>2110276096.20 26788613325.1733553799239.1844398370564.2048937938509.1851361431095.2058982491506.2000000;00E00V00j01801I01WS2LJ3LEN2HiS2LJ2H12H3S2LJ2W12H22H33LENS2LJ2H12H22H33LEN2HiS2LJ2W02H13LENS2LJ2H12H33LEN2HiS2LJ2H13LEN2Hi".
lia. }
  split; [split|].
  - cbn [cells_wf cell_wf]. split; [exact LEN| exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [lia|]. split; [rewrite LEN; lia|].
    intros i Hi. rewrite LEN in Hi.
    rewrite nth_error_firstn. replace (Nat.ltb i (Z.to_nat n')) with true by (symmetry; apply Nat.ltb_lt; exact Hi). rewrite nth_error_skipn.
    replace (a' + Z.of_nat i) with (a + Z.of_nat (Z.to_nat (a' - a) + i)) by lia. apply BY. lia.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|]. intros i Hi.
    replace (a' + i) with (a + (a' - a + i)) by lia. apply W. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma gshads_of_hull : forall G lo hi m a (k : nat) j, rw_cells asegs m a [CB k j] -> a <= lo -> hi <= a + Z.of_nat k ->
  gsorted lo hi G -> gshads m G.
Proof.
  induction G as [|[[[[b sz] swr] nm] md] G IH]; intros lo hi m a k j C H1 H2 S; cbn [gshads gsorted] in *; [exact I|].
  destruct S as (L1 & L2 & _ & _ & SW & _ & _ & S).
  Local Ltac2 Set LiaHints.tbl := fun () => "0060>12602440416.2229782446203.2143839256185.2158324979654.2263577466763.22748780348.21  00000700800<00F00M00NS2H22L2SS2SWS2H12L12N0S2H12L1S".
assert (N0 : 0 <= shn swr) by (unfold shn; rewrite Z.shiftr_div_pow2 by lia; apply Z.div_pos; lia).
  split.
  - eapply cb_sub; [exact C| lia| exact N0| lia].
  - eapply IH; [exact C| | exact H2| exact S]. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma gdescs_transport : forall G W m m' d, gdescs m d G -> munch W m m' -> wmono asegs m m' ->
  (forall A n, d <= A -> 0 <= n -> A + n <= d + 64 * Z.of_nat (length G) -> disjoint_from W A n) -> gdescs m' d G.
Proof.
  induction G as [|[[[[b sz] swr] nm] md] G IH]; intros W m m' d HG MU WM HD; cbn [gdescs length] in *; [exact I|].
  destruct HG as [[D1 D2] HG]. split; [split|].
  - Local Ltac2 Set LiaHints.tbl := fun () => "0090>12128333532.1817451922806.182424953317.23 28082131295.183080755707.23 33669200788.1841912482204.2346585200585.1868059072559.1800000100200600700;00<00@00A00BSSS2H2SS2H3SS2H1SS".
eapply rw_cells_transport; [exact D1| exact MU| exact WM| apply HD; cbn [cells_size csize Nat.add]; lia].
  - eapply rw_cells_transport; [exact D2| exact MU| exact WM| apply HD; cbn [cells_size csize Nat.add]; lia].
  - eapply IH; [exact HG| exact MU| exact WM|]. intros A n H1 H2 H3. apply HD; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma gshads_transport : forall G W m m' lo hi, gshads m G -> gsorted lo hi G -> munch W m m' -> wmono asegs m m' ->
  (forall A n, lo <= A -> 0 <= n -> A + n <= hi -> disjoint_from W A n) -> gshads m' G.
Proof.
  induction G as [|[[[[b sz] swr] nm] md] G IH]; intros W m m' lo hi HG S MU WM HD; cbn [gshads gsorted] in *; [exact I|].
  destruct HG as [[j C] HG]. destruct S as (L1 & L2 & _ & _ & SW & _ & _ & S).
  Local Ltac2 Set LiaHints.tbl := fun () => "0090>15875498245.242424953317.29 29784463594.2343845369576.2344206882378.2452369040876.2457491806763.2964576884989.24751285165.23  00000400800900=00A00E00O00P00QS2L1S2H2SS2SWS2L2S2N0S2L12N02H1SS".
assert (N0 : 0 <= shn swr) by (unfold shn; rewrite Z.shiftr_div_pow2 by lia; apply Z.div_pos; lia).
  split.
  - exists j. eapply rw_cells_transport; [exact C| exact MU| exact WM|]. apply HD; [lia| lia|]. cbn [cells_size csize].
    rewrite Nat.add_0_r, Z2Nat.id by lia. lia.
  - eapply IH; [exact HG| exact S| exact MU| exact WM|]. intros A n H1 H2 H3. apply HD; [lia| lia| exact H3].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Definition mdtor_pre (m : mem) : Prop :=
     mdtor_rt m
  /\ rw_cells asegs m 0x99ad8 [C8 (Z_to_bv 64 0x9d710); C8 (Z_to_bv 64 0x9d790)]     (* [comment removed for export] *)
  /\ rw_cells asegs m 0x9d7c0 [C8 (Z_to_bv 64 1)]                                     (* [comment removed for export] *)
  /\ rw_cells asegs m 0x9e730 [C8 (Z_to_bv 64 0)]                                     (* [comment removed for export] *)
  /\ gdescs m 0x9d710 AGLOBALS                                                        (* [comment removed for export] *)
  /\ (exists j, rw_cells asegs m 0x7fffc1a8 [CB 16 j])                               (* [comment removed for export] *)
  /\ (exists j, rw_cells asegs m 0x8000bae2 [CB 16 j]).                              (* [comment removed for export] *)

#[using="Type"] Lemma mdtor_pre_frame : forall sp m m',
  mdtor_pre m -> KHIGH <= sp - 48 - MDTOR_DEPTH -> munch (AEXIT_W1 sp) m m' -> wmono asegs m m' -> mdtor_pre m'.
Proof.
  intros sp m m' P KH MU WM. unfold KHIGH, MDTOR_DEPTH in KH.
  assert (D : forall A n, 0 <= n -> A + n <= 0x80014010 -> 0x5f4084 <= A \/ (0x9d811 <= A /\ A + n <= 0x5f3e60) \/ A + n <= 0x9d810 ->
              disjoint_from (AEXIT_W1 sp) A n).
  { intros A n Hn HA HO. unfold AEXIT_W1, MDTOR_DEPTH. cbn. Local Ltac2 Set LiaHints.tbl := fun () => "00E0>1302587838.18 15692952126.1817599773107.1821689057821.172424953317.23 28337422245.1330235520413.1733670935481.1834581281843.1841106776093.1741182222292.1744667713715.1854612051697.2354684058931.1856820137790.1859632997095.2363903571646.186520274589.17 67618108083.1868214804125.177888471230.18 00000100200300400800B00C00D00E00F00J00K00O00P00Q00U00V00W00X00Y00ZSSSSS2H2S2KH2HA2HOSSSSS2KHSS2H3SSS2H3SSSSS".
lia. }
  unfold mdtor_pre in *.
  destruct P as (RT & G1 & G2 & G3 & GD & [j1 S1] & [j2 S2]).
  assert (RT' : mdtor_rt m').
  { eapply mdtor_rt_frame; [exact RT | exact MU | exact WM | ]. unfold AEXIT_W1, MDTOR_DEPTH.
    repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. }
  refine (conj RT' _).
  split; [| split; [| split; [| split; [| split]]]].
  - eapply rw_cells_transport; [exact G1 | exact MU | exact WM | apply D; cbn; lia].
  - eapply rw_cells_transport; [exact G2 | exact MU | exact WM | apply D; cbn; lia].
  - eapply rw_cells_transport; [exact G3 | exact MU | exact WM | apply D; cbn; lia].
  - eapply gdescs_transport; [exact GD | exact MU | exact WM |]. rewrite AGLOBALS_length. intros A n H1 H2 H3. apply D; lia.
  - exists j1. eapply rw_cells_transport; [exact S1 | exact MU | exact WM | apply D; cbn; lia].
  - exists j2. eapply rw_cells_transport; [exact S2 | exact MU | exact WM | apply D; cbn; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End CANSEC2.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Ltac rt_split := unfold mdtor_rt; repeat match goal with |- _ /\ _ => split end; hyp_by_addr.
Ltac lit_nat := repeat match goal with H : rw_cells _ _ _ [CB (Z.to_nat (Zpos ?p)) _] |- _ =>
                  let v := eval vm_compute in (Z.to_nat (Zpos p)) in change (Z.to_nat (Zpos p)) with v in H; move H at top end.
Ltac lit_addr := repeat match goal with H : rw_cells _ _ (Zpos ?a + Zpos ?b) _ |- _ =>
                  let v := eval vm_compute in (Zpos a + Zpos b) in change (Zpos a + Zpos b) with v in H end.
Ltac lit_rng := repeat match goal with H : rng _ _ (Zpos ?a - Zpos ?b) |- _ =>
                  let v := eval vm_compute in (Zpos a - Zpos b) in change (Zpos a - Zpos b) with v in H end.
(* [comment removed for export] *)
Ltac side RIMG RSTK KH :=
  lazymatch goal with
  | |- evtF _ _ _ _ => idtac
  | |- rng _ _ _ => first [ assumption | eapply rng_sub'; [exact RSTK | lia] ]
  | |- rng_aimg _ => exact RIMG
  | |- rw_cells _ _ (?a + ?b) _ => let v := eval vm_compute in (a + b) in change (a + b) with v; hyp_by_addr
  | |- rw_cells _ _ _ _ => hyp_by_addr
  | |- mdtor_rt _ => rt_split
  | |- mem_inv _ _ => hyp_by_addr
  | |- stk _ _ _ _ => hyp_by_addr
  | |- @eq _ _ _ => reflexivity
  | |- Z.lt (shn _) _ => vm_compute; reflexivity
  | |- _ => first [exact KH | lia]
  end.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac hstepS := sort_lits; zstep; fix_lit_store.
Ltac astepS := hstepS; try (first [if_true | if_false]).

Section CANSEC2b. Context {rc : runConstT}.
#[using="Type"] Lemma munch_hull : forall lo hi a b m m', munch [(a, b)] m m' -> lo <= a -> b <= hi -> munch [(lo, hi)] m m'.
Proof.
  intros lo hi a b m m' M H1 H2. eapply munch_weaken; [| exact M]. unfold sub_fp. intros x Hx. cbn [outside] in *.
  destruct Hx as [Hx _]. Local Ltac2 Set LiaHints.tbl := fun () => "0010>40231916450.1200000:S2H12H22Hx".
split; [lia| exact I].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma munch_hull2 : forall lo hi a b m m1 m', munch [(lo, a)] m m1 -> munch [(b, hi)] m1 m' -> lo <= b -> a <= hi -> munch [(lo, hi)] m m'.
Proof.
  intros lo hi a b m m1 m' M1 M2 H H'. Local Ltac2 Set LiaHints.tbl := fun () => "0020>19678040670.1433642005373.1400000600=S1H2HxS2H'2Hx".
eapply munch_trans; [eapply munch_weaken; [| exact M1] | eapply munch_weaken; [| exact M2]];
    unfold sub_fp; intros x Hx; cbn [outside] in *; destruct Hx as [Hx _]; split; try exact I; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma unreg_loop : forall G RNG (lo hi d spv : Z) (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s8 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem),
  G <> [] ->
  mem_inv asegs m -> mdtor_rt m -> gdescs m d G -> gshads m G -> gsorted lo hi G ->
  0x10000 <= d -> d + 64 * Z.of_nat (length G) <= 0x5f6000 -> 0x7fffa000 <= lo -> hi <= 0x800cd000 -> 0 <= spv < 2^64 ->
  rng_aimg RNG -> rng RNG lo (hi - lo) ->
  evtF asegs RNG (fun ms' => exists (ra' t0' t1' t2' s0' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
      ms' = MS (mkR ra' (Z_to_bv 64 spv) gp tp t0' t1' t2' s0' (Z_to_bv 64 0x1329a8) a0' a1' a2' a3' a4' a5' a6' a7'
                    (Z_to_bv 64 2) (Z_to_bv 64 0x1b21d) (Z_to_bv 64 (d + 64 * Z.of_nat (length G))) s5 s6 (Z_to_bv 64 0x9acc0) s8
                    (Z_to_bv 64 0x9e678) (Z_to_bv 64 0xa0e78) (Z_to_bv 64 0) t3' t4' t5' t6')
               F (Z_to_bv 64 0x3f4a0) fc None m' (seg_rom asegs)
      /\ munch [(lo, hi)] m m' /\ wmono asegs m m' /\ mem_inv asegs m')
    (MS (mkR ra (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 (Z_to_bv 64 0x1329a8) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 2) (Z_to_bv 64 0x1b21d) (Z_to_bv 64 d) s5 s6 (Z_to_bv 64 0x9acc0) s8 (Z_to_bv 64 0x9e678)
             (Z_to_bv 64 0xa0e78) (Z_to_bv 64 (Z.of_nat (length G))) t3 t4 t5 t6)
        F (Z_to_bv 64 0x3f29c) fc None m (seg_rom asegs)).
Proof.
  induction G as [|[[[[b sz] swr] nm] md] G IH]; intros until m; intros NE MI RT HD HS HSO D0 D1 LO HI SPV RIMG RH; [congruence|].
  clear NE. cbn [gdescs gshads length] in *. pose proof HSO as HSO'. cbn [gsorted] in HSO'.
  destruct HD as [[DC DB] HD]. destruct HS as [[j SH] HS]. destruct HSO' as (L1 & L2 & AL & SL & SW & BL & BH & HSO').
  rewrite Nat2Z.inj_succ in D1 |- *.
  pose proof (Zle_0_nat (length G)) as LG.
  Local Ltac2 Set LiaHints.tbl := fun () => "00X0?11150279611.66 14892681432.96 15306844775.96 15873449912.93 15877545095.11716500635355.88 18375735985.90 19301059053.96 22063674542.66 2424953317.94  2728801115.66  27616505739.66 29603282131.66 29784530535.63 30090030831.96 30096696442.66 33513656266.93 33669004442.87 33935627387.66 34506992316.87 35253210252.96 37431855784.66 37529455908.93 38610020951.95 44200493303.93 44204786632.11745412888586.95 47404309994.11747988827160.64 48701252342.96 52061149739.94 52293735510.63 54612051697.94 54917223859.10257829424363.65 59709448941.11762512989918.11766110553915.10267770632493.1027853444906.96  00000700;00B00F00J00Q00[00\00`00d00h00l01001101601;01>01?01C01J01N01R01S01W01[01_01b01c01j02402>02E02L02M02T02U02\02]02g02kS2D12LGS2D1S2L12N0S2L1S2L1S2N02SBS2LO2L12HASS2D0S2H2S2ALS2SLS2SWSS3SPVS3SPVS1KSS2BHS2D12LGS2D0S2BLFS2H1S2L2S2L2S1KSS2LO2L1S2LO2L12N0S2D02D12LGS2SL2SWS2D12H3FS2L12L2SS2L12N0FS2D02D12LGS2HI".
assert (N0 : 0 < shn swr < 32) by (unfold shn; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  assert (SB : 0x7fffa000 <= shd b) by lia.
  assert (RX : rng RNG (shd b) (shn swr)) by (eapply rng_sub'; [exact RH| lia]).
  change (2^64 - 1) with 18446744073709551615 in DC.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (unreg_one_spec RNG (shd b) (shn swr)); first [exact MI | exact RT | exact DC | exact DB | exact SH | exact RIMG | exact RX
                                                        | reflexivity | lia]. }
  intros ms1 PO1. unfold unreg_one_post in PO1.
  destruct PO1 as (t0' & t1' & t2' & s0' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1 & MI1 & _).
  (* [comment removed for export] *)
  assert (DJ : forall A n, 0 <= n -> A + n <= 0x5f6000 -> disjoint_from [(shd b, shd b + shn swr)] A n).
  { intros A n Hn HA. cbn [disjoint_from]. split; [left; lia| exact I]. }
  pose proof (rw_cells_transport asegs _ _ _ _ _ DC MU1 WM1 ltac:(apply DJ; cbn [cells_size csize Nat.add]; lia)) as DC1.
  assert (RT1 : mdtor_rt m1).
  { eapply mdtor_rt_frame; [exact RT| exact MU1| exact WM1|]. apply Forall_cons; [| apply Forall_nil]. cbn [rt_clear]. lia. }
  assert (HD1 : gdescs m1 (d + 64) G).
  { eapply gdescs_transport; [exact HD| exact MU1| exact WM1|]. intros A n H1 H2 H3. apply DJ; lia. }
  assert (HS1 : gshads m1 G).
  { eapply gshads_transport; [exact HS| exact HSO'| exact MU1| exact WM1|]. intros A n H1 H2 H3. cbn [disjoint_from]. split; [right; lia| exact I]. }
  clear DC DB SH HD HS RT MI.
  pose proof RT1 as RT1'. destruct RT1' as (PGC & GOT & GOT80 & REAL & SHB & INI & CANP & THR & RGL).
  (* [comment removed for export] *)
  hstepS. hstepS. astepS. hstepS. hstepS. hstepS.
  if_cases K; zify_cond K.
  - (* [comment removed for export] *)
    destruct G as [|g G]; [| cbn [length] in K; rewrite Nat2Z.inj_succ in K; lia].
    apply evtF_done. cbn [length]. do 18 eexists.
    split; [reflexivity|].
    split; [eapply munch_hull; [exact MU1| lia| lia]|]. split; [exact WM1| exact MI1].
  - (* [comment removed for export] *)
    destruct G as [|g G]; [cbn [length] in K; lia|].
    set (G' := g :: G) in *.
    (* [comment removed for export] *)
    match goal with |- context [Z_to_bv 64 (Z.succ (Z.of_nat (length G')) + ?c)] =>
      replace (Z_to_bv 64 (Z.succ (Z.of_nat (length G')) + c)) with (Z_to_bv 64 (Z.of_nat (length G'))) by (f_equal; lia) end.
    eapply evtF_mono.
    { eapply (IH RNG (shd b + shn swr) hi (d + 64)); first [ discriminate | exact MI1 | exact RT1 | exact HD1 | exact HS1 | exact HSO'
                                                          | exact RIMG | eapply rng_sub'; [exact RH| lia] | lia ]. }
    cbv beta. intros ms' (ra' & t0'' & t1'' & t2'' & s0'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m' & -> & MU2 & WM2 & MI2).
    exists ra', t0'', t1'', t2'', s0'', a0'', a1'', a2'', a3'', a4'', a5'', a6'', a7'', t3'', t4'', t5'', t6'', m'.
    split; [ match goal with |- context [Z_to_bv 64 (d + 64 * Z.succ (Z.of_nat (length G')))] =>
               replace (d + 64 * Z.succ (Z.of_nat (length G'))) with (d + 64 + 64 * Z.of_nat (length G')) by lia end;
             reflexivity |].
    split; [eapply (munch_hull2 lo hi (shd b + shn swr) (shd b + shn swr)); [eapply munch_hull; [exact MU1| lia| lia] | exact MU2 | lia | lia]|].
    split; [eapply wmono_trans; [exact WM1| exact WM2]| exact MI2].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC2b.

(* [comment removed for export] *)
Ltac hstep ::= zstep; fix_lit_store.

Section CANSEC3. Context {rc : runConstT}.
#[using="Type"] Theorem module_dtor_proof : module_dtor_stmt mdtor_pre.
Proof.
  unfold module_dtor_stmt. intros until lo. intros HPRE ST LO KH MI RSTK RIMG RW.
  pose proof KH as KH'. unfold KHIGH in KH'. unfold MDTOR_DEPTH in LO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof HPRE as P. unfold mdtor_pre in P.
  destruct P as (RT & GSS & FLG & MTX & GD & [j1 S1] & [j2 S2]).
  pose proof RT as RT'. destruct RT' as (PGC & GOT & GOT80 & REAL & SHB & INI & CANP & THR & RGL).
  (* [comment removed for export] *)
  unfold MDTOR_W in RW.
  repeat lazymatch type of RW with Forall _ (_ :: _) =>
    let H := fresh "RW" in pose proof (Forall_inv RW) as H; cbn [fst snd] in H; apply Forall_inv_tail in RW end.
  lit_rng.
  pose proof (munch_refl [(bv_unsigned sp - 1024, bv_unsigned sp); (0x9d7c0, 0x9d7c8); (0x9e730, 0x9e738);
              (0x7fffc1a8, 0x7fffc1b8); (0x8000bae2, 0x8000baf2)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  Local Ltac2 Set LiaHints.tbl := fun () => "09`0?10039552492.88 10088628586.12110103563544.91 10188553603.87 10506933272.91 10685224615.89 1079682851.117 10862393880.90 10972410904.91 11110357784.91 11362458803.90 11364905112.90 11475098008.90 11504437656.90 11508929048.90 11633885848.90 11696657560.90 11854458228.11211854458228.83 12163290648.92 12237445648.10212362200856.89 12428150072.11612543972632.91 12836051736.91 12874445464.90 13000380547.11813000380547.89 13092900324.86 13146522052.77 13163206680.84 13163206680.87 13163206680.94 13201275160.92 13409264536.90 13651810739.87 13651810739.94 13655953176.92 1371286659.115 1371286659.86  13949724851.91 13954434065.11714201179716.79 14224430925.10814377232691.90 14386403300.86 14386403301.11614404687680.88 14613807384.92 14921199539.90 14980397443.11714980397443.87 15045052203.90 15074360607.10215104381976.92 15169268888.94 15452344984.90 15478876952.90 15593142936.91 15670301260.86 15795316387.11715856406132.11916167008024.89 16213386675.92 16351888607.10116351888607.10216528340147.89 16641156659.90 16855241752.91 16897753792.88 16955585843.90 17031003544.90 17088905368.92 17288173208.94 17371454872.90 17428462744.90 17470326639.11217470326639.83 17499552691.91 17632133144.92 17927060531.90 18081674008.91 18116785944.92 18159873944.90 18187652120.91 18214550040.91 18265732580.11418265732580.84 18548711960.92 18618292611.12318618292611.91 18792264115.92 18840727960.90 18976317807.11919006120615.84 19042827563.91 19066511015.89 19145457048.90 19208070823.87 19219771955.90 19315854943.1021933448932.115 1933448932.86  19463147231.10219471543192.90 19482963480.91 19619045547.89 19630331032.90 19772541407.10219878155416.90 19992479000.92 20026862744.90 20084426675.89 20406904000.90 20433961190.74 20514293811.90 20517883544.94 20540342678.11220673725464.84 20673725464.87 20673725464.94 20707147295.10220805123751.87 20944728600.89 21050193560.90 21144248856.84 21144248856.87 21144248856.94 21207973122.10821541434755.11621541434755.87 21684296856.90 21781323315.90 2185261208.90  21880434712.89 21995974936.92 22067285016.91 22067993779.92 22193440237.10722290347171.11722357826550.11222362160920.90 22519161511.87 22779918217.11122779918217.82 22911399320.90 22931427392.88 23077509607.87 23259527847.86 23360180915.90 2351266880.88  23658004888.89 23790048051.94 24137367320.90 24153062424.92 24188925208.92 2422572184.90  24646346931.91 24925778200.92 25052547224.90 25073854771.90 25076071819.11725355543319.80 25435258127.11525435258127.85 25482792915.79 25499053592.90 25566553219.11425566553219.84 25624113075.92 25732997144.92 25785063811.11725785063811.87 25939066547.91 26347796504.90 26368409395.90 26420023788.88 26424324672.88 26479497752.90 26700140056.90 26741471384.90 27147338155.93 27233612979.92 27370516120.90 27439898422.98 27442097076.81 2749330817.121 27519429784.90 27578957172.11227578957172.83 27624122904.84 27624122904.87 27624122904.94 27661120819.90 27681188262.77 27983689752.90 28072922155.89 28141822063.11228141822063.83 28174536216.91 28201875736.90 28202990515.91 28232796652.88 28514320536.90 28525327128.91 28630498355.90 28913119921.12128928117555.90 28947464871.88 28950691264.88 29142842027.89 29174389228.88 29371901571.10329371901571.89 29478243480.90 29596973080.90 2961124447.102 29692545944.92 29714896536.90 29737833181.12129846763672.90 29861645976.90 30007896984.90 30090674789.10230090674794.88 30093845803.91 30189236903.91 30454027800.91 30600218264.90 30665193763.11730727106968.94 30789699507.92 3083421208.89  30995698343.87 31161366443.89 31164578328.89 31217207347.90 31251757592.92 31389706136.90 31399093385.10531495617944.90 31562805016.90 31617443167.10231674167832.92 31700038511.11231700038511.83 32005657752.90 32086382488.90 32170890648.91 32247030252.88 32460070848.90 32614775744.82 32797150580.11232797150580.83 33078744856.90 33489544031.10233510003693.10633750752536.90 33766159000.90 33865953688.90 33971183717.87 33971183723.11833999888408.92 34221083764.11934383631000.90 34585862040.90 34840976024.90 34894844291.10234894844291.87 3491948056.92  34951301952.88 3499374488.90  35001395692.88 35039397144.90 35069552792.90 35138195087.94 35572738328.92 36251137816.90 36574674563.11936574674563.88 36606830211.11936606830211.89 36859886744.90 37062796780.88 37238554472.90 37245778797.10837247578328.77 37247578331.79 37247661040.10837247661040.79 37504724647.91 37526138648.90 37728118936.90 37751770008.90 378738307.87   38172936619.89 3830064277.106 38362731800.92 38467250200.84 38467250200.87 38467250200.94 38479588672.88 38638915224.90 38685481752.92 38789230232.90 38903098019.11738938728820.11938956189976.90 39123711019.88 39242478692.86 3938769889.122 3940867048.90  39563569944.91 3974170136.92  39941648665.10739946321012.11940046219415.71 40158618216.12140540307045.87 40540307050.11740597171096.90 40618177816.91 40716109976.92 40809417112.90 40970295488.89 41033699096.92 41100924184.91 41117850981.87 41117850986.11741253204504.90 4131544713.118 41459949172.11941983056280.94 42495348204.88 42766495640.90 42805740039.11642846560664.90 43061379371.72 43121191467.91 43122952810.88 43122952811.11843275941236.11243275941236.83 43492410392.92 43507384707.11643507384707.87 43527117080.90 43605444632.90 44075152536.90 44420783207.11344420783207.83 44461400984.90 44553499231.10244624256280.84 44624256280.87 44624256280.94 44673306904.92 44732399896.92 44899205912.91 44943623064.90 44964803431.11244964803431.80 45030765208.90 45033554584.90 45093806515.90 45121470488.89 45180246296.92 45380827299.11745484308248.92 45487759923.94 46003364632.90 46235924760.84 46235924760.87 46235924760.94 46390321508.86 46392837507.11746392837507.87 46426126431.10246665936756.11246665936756.83 47006590528.88 47235946392.90 47638924696.90 47658328856.91 47678950835.91 47688149866.11747688149866.88 47700500248.90 47869631896.90 47900152984.94 47955047576.90 47963715864.92 48075001395.90 48089218200.90 48199399523.11748529832177.11048529832177.81 4876052416.92  48893238296.91 49287947544.91 49345969283.87 49409381016.90 49491439640.92 49533429272.94 4986721944.90  49957961496.90 50022562840.90 50024834968.90 50069891224.90 5014251800.92  50207128.90    50221560344.90 50269882218.11750269882218.88 50305698327.88 50318749080.90 50543022872.91 50653354547.90 50664164139.89 50677792280.92 5072571819.89  50749557528.91 50771321240.90 51234361003.89 51465110936.90 51567446375.11451567446375.85 51693436583.87 5170374848.85  51896122520.90 51949351448.84 51949351448.87 51949351448.94 52076332701.11952085918705.11752108408216.90 52138178584.92 52151318827.90 52309552244.11952355859864.94 52363845748.11952553219883.94 52577538839.11252577538839.11952577538839.83 52577538839.84 52577538839.87 52577538839.88 52577538839.89 52577538839.90 52577538839.91 52577538839.92 52577538839.94 52614868698.94 52615423000.91 52987303192.91 53032137664.90 53221810200.89 53428579224.90 53477050648.92 53510313876.11653511590552.90 5368629927.88  53816577816.91 53951985688.92 54024088963.87 54140369575.87 54157462680.90 54164510851.11354164510851.81 54196881432.90 54509322919.87 55238157483.89 55482343576.90 55496111076.10155539535476.11255539535476.83 55605846424.94 55606215043.11655606215043.87 55890146712.90 55993395608.94 56170414366.94 56318259480.92 56524740032.87 56748692340.11256748692340.83 56964914855.89 57006501400.92 57137128088.90 57303947553.98 57387588263.87 57413815412.1195760890719.102 57766271107.91 57799592543.10257915518083.11857915518083.88 57937621272.84 57937621272.87 57937621272.94 58135773316.75 58199852451.11758323164323.11758416582516.11258416582516.83 58459745811.80 58477402019.11758547856664.91 59051098432.88 59085150616.90 59178106163.85 59588178609.12159817589016.91 60037858456.90 6014957611.90  60276305268.11260276305268.83 60335527832.90 60647885491.94 60662996376.90 6067700632.84  6067700632.87  6067700632.94  6076365731.117 61262187744.77 61262187747.79 6141143156.119 61542075584.90 61592356519.88 61801762840.91 61956786712.91 62295638808.92 62389933940.83 62549928615.87 62560510784.88 62644762008.94 62819576600.91 62859994604.88 62925078168.90 63036737944.90 63121482136.90 63131866776.90 63226762931.92 63566088088.90 63620716339.90 63780537836.88 63787697900.88 63801148440.92 639945956.115  639945956.86   64031827864.90 64261731243.89 6446145560.92  6452514840.89  65051750080.89 65212743211.83 65212743211.86 65212743211.93 65316957080.90 65394275224.90 65508437732.10165508437732.86 65530800136.10865567805059.11865567805059.88 65626505624.90 65788601011.92 65972654703.11965995525528.90 6615494311.89  66215846707.90 66282688408.92 66360358380.88 66721159227.84 66729985816.90 66772627111.87 66806001892.86 66825358360.92 66980406808.90 67081926311.81 67133297176.92 67136312999.87 67157832433.12167168426264.92 67374224536.90 67551377526.11467578108480.92 67665400728.90 67819218968.90 68094715463.77 68296392820.11968402691956.11268402691956.83 6931027736.89  6959146392.94  7238556388.115 7238556388.86  7244508312.90  7463989144.90  7502079531.91  773468312.90   7786772964.86  7786772965.116 7845783192.90  7869728152.94  7878658584.92  7928503960.90  8047462936.84  8047462936.87  8047462936.94  83611443.90    8387529152.89  8496163352.84  8496163352.87  8496163352.94  8586775704.91  8603416747.89  9080374244.86  9080374245.116 9182076952.89  9627307544.91  9791719555.118 9791719555.89  00000800900A00B00J00K00W00_00g00o01001801@01H01P01X01`01a01b01j01k02302402<02D02L02M02N02O02P02X02`02h03003803903:03B03C03D03E03Q03R03S03T03U03V03Z03b03c03d03e03j04204:04B04J04R04Z04^04j04k05305405505605705805@05D05E05M05U05]05e05m06506=06>06F06G06O06W06_06g06o07007107907:07;07<07D07L07M07R07S07[07\07]07^07_07`07a07i08108608>08?08G08O08W08X08\08]08^08f08g08o09709?09@09A09I09Q09Y09a09i09j09k09l0:40:50:=0:E0:M0:U0:V0:W0:c0:d0:l0:m0:n0:o0;70;;0;@0;A0;B0;F0;N0;O0;W0;_0;g0;o0<00<80<@0<A0<M0<N0<O0<P0<Q0<Y0<Z0<[0<\0<d0<e0<f0<g0<o0=00=80=<0=D0=L0=T0=Y0=Z0=b0>00><0>=0>E0>F0>G0>O0>W0>_0>`0>d0>l0?10?90?A0?I0?Q0?R0?Z0?b0?j0?k0?l0?m0?n0@20@70@?0@@0@A0@I0@Q0@R0@Z0@b0@c0@k0A30A;0A<0A=0AB0AC0AK0AS0A_0Ag0Ah0B00B10B60B>0B?0BG0BO0BP0BX0B`0Ba0Bi0C10C90CA0CI0CQ0CY0C]0Ca0Cb0Cc0Ck0Cl0Cm0D50D=0DE0DF0DG0DO0DP0DX0D`0Dh0Di0Dj0E20E60E>0EF0EN0EV0EW0E_0Eg0Eh0Ei0Ej0Ek0F30F;0F<0F=0F>0F?0F@0FA0FB0FJ0FR0FZ0F[0F`0Fd0Fl0G40G<0GD0GH0GP0GX0G`0Gl0Gm0H50H:0H;0H<0H=0HE0HM0HQ0HR0HV0HW0HX0HY0Ha0Hi0I10I90I=0IE0IM0IN0IO0IW0IX0IY0Ia0Ii0J10J20J:0J>0JC0JD0JE0JF0JG0JO0JP0JQ0JY0Ja0Ji0Jj0Jk0K30K40K<0KD0KL0KT0K\0Kd0Kl0Km0Kn0L60L>0L?0LG0LO0L[0Lc0Ld0Ll0M40M<0MD0ME0MF0MG0MH0MI0MJ0MN0MV0M^0Mf0Mg0Mh0Mi0N10N90N=0NE0NM0NN0NV0Nb0Nc0Nd0Nh0O00O80O90OA0OI0OQ0OY0Oa0Oi0P10P90PA0PI0PQ0PR0PS0PT0P\0Pd0Pe0Pj0Q20Q70Q?0QG0QL0QT0QU0QV0QW0Q[0Qc0Qk0R30R;0R<0R=0RE0RM0RR0RS0R[0R\0R]0R^0R_0R`0Ra0Rb0Rc0Rd0Re0Rf0Rg0Rh0Ri0S10S90S=0SE0SM0SU0SV0S^0S_0Sg0So0T00T10T90T:0T;0TC0TD0TI0TQ0TV0TW0TX0T`0Ta0Tb0Tj0U20U30U;0U?0U@0UA0UB0UJ0UR0US0UT0UU0UV0UW0UX0UY0UZ0Ub0Uj0V20V60VB0VN0VO0VP0VQ0V]0Ve0Vi0W10W20W30W;0WC0WH0WI0WJ0WR0WS0W[0Wc0Wk0X30X?0X@0XA0XB0XF0XG0XO0XW0X_0X`0Xa0Xe0Xm0Y50Y=0YE0YM0YU0Y]0Y^0Yf0Yg0Yo0Z70Z?0Z@0ZA0ZI0ZN0ZV0Z^0Zb0Zg0Zl0[10[90[A0[B0[C0[G0[H0[I0[Q0[R0[Z0[b0[c0[d0[l0\40\?0\G0\H0\I0\Q0\Y0\Z0\b0\c0\d0\l0]40]50]90]A0]I0]J0]K0]L0]M0]U0]]0]^0]_0]g0]o0^40^<0^=0^>0^F0^N0^V0^^0^f0^n0_60_70_;0_C0_K0_S0_[0_`0_a0_b0_j0`20`30`4S2LO3KH'SS2LO3KH'SS2LO3KH'SS2LO3KH'3HspS2LO3KH'S2LO3KH'S2LO3KH'SS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'SSS2LO3KH'FS2LO3KH'FS2LO3KH'S2LO3KH'S2LO3KH'SSSFS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'SSS2LO3KH'SSSS2LO3KH'3HspSFSSSS2HBS2LO3KH'SSSS3RSPS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2HBS2LO3KH'3HspSS2LO3KH'SSSSSS2LO3KH'S2HBSS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'SS2LO3KH'SS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'SSS2LO3KH'SSSS2LO3KH'S2LO3KH'SS3RSPSS2LO3KH'SSSSSSS2LO3KH'S2LO3KH'S3RSPS2LO3KH'FS2LO3KH'S2LO3KH'S2LO3KH'SS2HBSSS2LO3KH'SS2LO3KH'S2LO3KH'S2LO3KH'SSS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'FSSS2LO3KH'SS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'SSS2LO3KH'3HspSS2LO3KH'SSSS2LO3KH'S2HBS3RSPSSS2HBS2LO3KH'SS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'SS2LO3KH'S2LO3KH'SS2LO3KH'3HspSSSFS2LO3KH'SSSS2LO3KH'SSSS2LO3KH'SS2LO3KH'S2HBS2LO3KH'S2LO3KH'S2LO3KH'S3RSPSS2LO3KH'S2LO3KH'3RSP1HS2LO3KH'3RSPFS2LO3KH'SSS2LO3KH'S2LO3KH'S2LO3KH'SS2LOS2LO3KH'S3RSPS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'SS2LO3KH'S2LO3KH'S2LO3KH'SSSSS2HBS3RSPS2LO3KH'SSS2LO3KH'S2LO3KH'SS2LO3KH'S2LO3KH'FS2LO3KH'S2LO3KH'S2LO3KH'SSS3RSPSS2LO3KH'S2LO3KH'S2LO3KH'3HspS2LO3KH'SS2LO3KH'SS3RSPS2LO3KH'SS2LO3KH'S2LO3KH'SS2LO3KH'S2LO3KH'SS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2HBS2HBSSS2LO3KH'SSS2LO3KH'S2LO3KH'S2LO3KH'SSS2LO3KH'SS2LO3KH'S2LO3KH'S2LO3KH'SSS2LO3KH'S2HBS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'SS2LO3KH'S2LO3KH'SSSSS2LO3KH'S2LO3KH'SFFFFFSS2LO3KH'S2LO3KH'S2LO3KH'SS3RSPS2LOS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2HBS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'3HspSS2LO3KH'S3RSPSSSS2LO3KH'S2LO3KH'S2LOSS2LOSSSS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2HBS2LO3KH'S2LO3KH'SSS2LO3KH'SSS2LO3KH'S2LO3KH'S2LO3KH'FS2LO3KH'S2LOS3RSPSSSSS2LO3KH'SSS2LO3KH'S2LO3KH'S2LO3KH'SSS2LO3KH'SS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'SSS2LO3KH'S2LO3KH'SS2LO3KH'S2LO3KH'S2LO3KH'3HspS2LO3KH'SS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'SSSSSSS2HBS2LO3KH'S2LO3KH'S2LO3KH'SSSS2LO3KH'S2LO3KH'S2LOS2LO3KH'S2LO3KH'SS2LO3KH'S2LO3KH'3HspSSS2HBS2LO3KH'S2LO3KH'SS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'SSSS2LO3KH'S2LO3KH'SS3RSPS2LO3KH'S3RSPS2LO3KH'S2LO3KH'S3RSPS2LO3KH'SSSS2HBS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'FSS2LO3KH'S2LO3KH'S3RSPSS2LO3KH'SSSSSSSSSSSSSSS2LO3KH'S2LO3KH'S2HBS2LO3KH'S2LO3KH'S2LO3KH'SS2LO3KH'SS2LO3KH'S2LO3KH'SSS2LO3KH'SSS2LO3KH'SS3RSPS2LO3KH'S3KH'SSS2LO3KH'SSS2LO3KH'S2LO3KH'SS2LO3KH'S2HBSSSS2LO3KH'S2LO3KH'FSSSSSSSS2LO3KH'S2LO3KH'S2LO3KH'S2LOS2LO3KH'3HspS2LO3KH'3HspSSSS2LO3KH'3HspS2LO3KH'S2HBS2LO3KH'SSS2LO3KH'S2LO3KH'S3RSPSSS2LO3KH'SS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'3HspFFSS2HBSS2LO3KH'S2LO3KH'S2LO3KH'SSS2HBS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'SS2LO3KH'SS2LO3KH'S2LO3KH'S2LO3KH'SSS2LO3KH'S3RSPS2LO3KH'S2LO3KH'S2HBS3RSPS3RSPS3RSPS2LO3KH'S2LO3KH'SSS2LOSSS2LO3KH'SS2LO3KH'S2LO3KH'SSS2LO3KH'S2LO3KH'S2LO3KH'2H3S2LO3KH'SSS2LO3KH'S2LO3KH'SS2LO3KH'SSS2LO3KH'S2LO3KH'SS2HBS2LO3KH'S2LO3KH'SSSSS2LO3KH'S2LO3KH'SSS2LO3KH'S2LO3KH'S3RSPS2LO3KH'SSS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'SS2HBS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S3RSPSSS2LO3KH'S2LO3KH'SS".
assert (RSF : rng RNG (bv_unsigned sp + -272) 272) by (eapply rng_sub'; [exact RSTK | lia]). move RIMG at bottom.
  sort_lits. move S1 at top. move S2 at top.
  (* [comment removed for export] *)
  carve_frame 16%nat ST.
  do 9 hstep.
  (* [comment removed for export] *)
  carve_frame 16%nat ST.
  do 3 hstep. astep. hstep. hstep. astep. do 2 hstep. astep. do 4 hstep.
  (* [comment removed for export] *)
  carve_frame 176%nat ST.
  do 14 hstep.
  do 5 hstep.                                          (* [comment removed for export] *)
  replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (vm_compute; reflexivity).
  astep.                                               (* [comment removed for export] *)
  (* [comment removed for export] *)
  steps_to 0x3f188%Z.
  amo_step. astep. amo_step. astep. astep.
  move MTX after RGL.                                  (* [comment removed for export] *)
  (* [comment removed for export] *)
  hstep. hstep. astep.
  steps_to 0x3f29c%Z.
  (* [comment removed for export] *)
  lazymatch goal with M : munch _ m ?mc, W : wmono _ m ?mc |- _ =>
    assert (GD' : gdescs mc 0x9d710 AGLOBALS)
      by (eapply gdescs_transport; [exact GD| exact M| exact W| rewrite AGLOBALS_length; intros A n H1 H2 H3; cbn [disjoint_from]; lia]) end.
  assert (HS : gshads _ AGLOBALS) by (eapply (gshads_of_hull AGLOBALS 0x7fffc1a8 0x7fffc1b8); [exact S1| lia| lia| exact AGLOBALS_sorted]).
  replace (Z_to_bv 64 2) with (Z_to_bv 64 (Z.of_nat (length AGLOBALS))) by reflexivity.
  move RW2 at bottom.
  call (unreg_loop AGLOBALS RNG 0x7fffc1a8 0x7fffc1b8 0x9d710).
  all: first [ unfold AGLOBALS; discriminate | exact GD' | exact HS | exact AGLOBALS_sorted | rewrite AGLOBALS_length; lia | side RIMG RSTK KH ].
  clear RW2 GD GD' HS.
  rewrite AGLOBALS_length.
  (* [comment removed for export] *)
  do 6 hstep. hstep.
  move RW3 at bottom.
  call_sp (poison_low_spec RNG 0x8000bae2 16). all: side RIMG RSTK KH. clear RW3.
  lit_nat.
  (* [comment removed for export] *)
  steps_to 0x3f4f8%Z.
  amo_step. astep. amo_step. astep. astep.
  astep.                                               (* [comment removed for export] *)
  steps_to 0x3f750%Z.
  (* [comment removed for export] *)
  match goal with H : rw_cells _ _ (bv_unsigned sp + -208) _, S : stk _ _ lo _ |- _ => release_frame H S (bv_unsigned sp + -32) end.
  hstep. hstep. hstep. hstep.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -32) _, S : stk _ _ lo _ |- _ => release_frame H S (bv_unsigned sp + -16) end.
  hstep. hstep. hstep.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -16) _, S : stk _ _ lo _ |- _ => release_frame H S (bv_unsigned sp) end.
  hstep.
  unfold module_dtor_post. sys_finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Closed.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Hypothesis get_set : forall s so, get_so (set_so so s) = so.
  Hypothesis set_set : forall s so so', set_so so' (set_so so s) = set_so so' s.
  Hypothesis set_get : forall s, set_so (get_so s) s = s.

  Definition aexit_spec_closed :=
    aexit_spec get_so set_so mdtor_pre module_dtor_proof mdtor_pre_frame
               (F_stdio_exit.stdio_exit_proof get_so set_so get_set set_set set_get).
End Closed.
End CANSEC3.