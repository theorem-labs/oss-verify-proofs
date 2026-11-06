(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim Monad Stdio Driver.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import Shadow ITreeA.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg F_syscalls StdioFiles Stdio_kit MonadF F_memset AExit F_stdio_exit.
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
  repeat (match goal with H : rw_cells bsegs _ (Zpos ?p) _ |- _ =>
            tryif (match goal with H' : rw_cells bsegs _ (Zpos ?p') _ |- _ =>
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
     rw_cells bsegs m 0x98ff0 [C8 (Z_to_bv 64 0x130ae0)]                                        (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x99000 [C8 (Z_to_bv 64 0x132b68); C8 (Z_to_bv 64 0x9e838); C8 (Z_to_bv 64 0xa1038);
                                C8 (Z_to_bv 64 0xa1d28); C8 (Z_to_bv 64 0xa1d30); C8 (Z_to_bv 64 0xa1d20)]  (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x99030 [C8 (Z_to_bv 64 0x9ae98)]                                        (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x9ae90 [C8 (Z_to_bv 64 0x92340); C8 (Z_to_bv 64 0x92744)]              (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xa1038 [C8 (Z_to_bv 64 0x7fff8000)]                                      (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xa1d18 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]                              (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xa089c [C1 (Z_to_bv 8 1)]                                                (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x132be0 [C8 (Z_to_bv 64 0xffffffffffffffff)]                                         (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x9e850 [C4 (Z_to_bv 64 1)].                                              (* [comment removed for export] *)

(* [comment removed for export] *)
Definition rt_clear (iv : Z * Z) : Prop :=
  let (lo, hi) := iv in
  lo <= hi /\
  (hi <= 0x98ff0 \/ (0x99038 <= lo /\ hi <= 0x9ae90) \/ (0x9aea0 <= lo /\ hi <= 0x9e850) \/ (0x9e854 <= lo /\ hi <= 0xa089c)
   \/ (0xa089d <= lo /\ hi <= 0xa1038) \/ (0xa1040 <= lo /\ hi <= 0xa1d18) \/ (0xa1d1a <= lo /\ hi <= 0x132be0) \/ 0x132be8 <= lo).

#[using="Type"] Lemma mdtor_rt_frame : forall m m' W,
  mdtor_rt m -> munch W m m' -> wmono bsegs m m' ->
  Forall rt_clear W -> mdtor_rt m'.
Proof.
  intros m m' W PC MU WM HW.
  assert (D : forall A n, 0 <= n ->
             ((0x98ff0 <= A /\ A + n <= 0x99038) \/ (0x9ae90 <= A /\ A + n <= 0x9aea0) \/ (0x9e850 <= A /\ A + n <= 0x9e854)
              \/ (0xa089c <= A /\ A + n <= 0xa089d) \/ (0xa1038 <= A /\ A + n <= 0xa1040) \/ (0xa1d18 <= A /\ A + n <= 0xa1d1a)
              \/ (0x132be0 <= A /\ A + n <= 0x132be8)) -> disjoint_from W A n).
  { intros A n Hn HA. clear MU. induction HW as [|[lo hi] W H1 H2 IH]; cbn in *; [exact I|]. split; [lia| exact IH]. }
  unfold mdtor_rt in *.
  destruct PC as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
  repeat match goal with |- _ /\ _ => split end; (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply D; cbn; lia]).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition poison_low_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (sb sl lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (sb, sb + sl)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' sb [CB (Z.to_nat sl) (repeat (Z_to_bv 8 0) (Z.to_nat sl))].

#[using="Type"] Lemma poison_low_spec : forall RNG (sb sl : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (addr size lo : Z) (junk : list byte),
  stk bsegs m lo (bv_unsigned sp) -> KHIGH <= lo -> lo <= bv_unsigned sp - 64 ->
  mem_inv bsegs m ->
  mdtor_rt m ->
  a0 = Z_to_bv 64 addr -> a1 = Z_to_bv 64 size -> a2 = Z_to_bv 64 0 ->
  addr mod 8 = 0 -> size mod 8 = 0 -> 0 < size -> 0x10000 <= addr -> addr + size <= 0x5f6000 -> shn size < 0x10000 ->
  sb = shd addr -> sl = shn size ->
  rw_cells bsegs m sb [CB (Z.to_nat sl) junk] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG sb sl ->
  evtF bsegs RNG (poison_low_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc sb sl lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x52f74) fc None m (seg_rom bsegs)).
Proof.
  intros until junk. intros ST KH LO MI RT -> -> -> AL SL SZ LOW HIE SMALL -> -> DST RIMG RSTK RSH.
  unfold KHIGH in KH. pose proof RT as RT'. destruct RT' as (PGC & GOT & GOT80 & REAL & SHB & INI & CANP & THR & RGL).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (shd addr, shd addr + shn size)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (SHR : 0x7fffa000 <= shd addr /\ shd addr + shn size <= 0x800cd000 /\ 0 < shn size).
  { unfold shd, shn, SHOFF. Local Ltac2 Set LiaHints.tbl := fun () => "02H0>1102156782.77 11767785710.7411801259171.93118736110.74  11912744615.7612334040174.7612367362435.7612367362435.8213021749692.7613219133678.7714159447534.761527479463.74 17141182446.7717646078182.6717776320430.8217776320431.7519007305966.7719049469500.761931560046.76 19382814446.7719415681262.7419447567726.7619618399904.8720633589486.7421918414723.7621918414723.8322748771310.7723026532974.7623814431342.7624559830510.7624630998586.7424982578106.7124982578737.6925071629079.7425071629079.7625071629079.7725314760359.7625878270254.8225878270255.7526074863037.7226082619953.802728429678.76 28913119922.8129784417117.6929784418006.7129784612193.6329786514270.7329794353372.8730365895150.7630396535790.7730862862062.7731081687356.7732595612014.7632651489978.7632825261550.7633039531175.7733486665994.7733680001082.7734056952330.7735281116398.7635499796014.7336115622446.7636115622446.8236423573305.9536674889838.7636993589379.7736993589379.8337107179452.7637390157038.7437728604022.813787933806.76 3945979267.76 3945979267.82 40194010222.7641362836762.6341809558659.7441809558659.8141843714542.7642501437472.8742501437473.8642503534633.7942511604512.7042995994990.7643060403331.7743060403331.8343061415849.6543987951406.7643987951406.8244483185911.9444750652170.7644804625134.7745221239098.7645257912942.7645607773934.7745751589358.7746262085614.764932169326.76 49343888933.9550101244526.765012112366.76 50565006190.7651172767598.7751481786499.7651481786499.8352076332701.8053620364910.7753767577775.7553767577775.8155207105262.7755737922668.9355748147788.7455750620234.7456066145674.7656228262055.7656238753134.76563227834.76  5638167690.74 5652583082.93 56582466030.7657745675194.7658512233326.7658838550766.7459308628433.7059308629336.7259308632823.7459310725459.7359391397898.7459445487498.7659588178610.8159748865774.7460025031335.7761082215790.7661917199023.7561917199023.8163235321900.7363235321900.8063249165934.7663694018620.7763766009966.7664556005486.7664601217390.7465088762478.7665098632080.786642473454.77 66761942666.766736605166.77 67800801447.7667943285742.7668010266983.737010956092.74 8583720762.77 985337532.76  00000700>00I00P00Q00X00Y00Z00^00e00l00m01401501901=01D01H01O01V01]01d01e01l01m01n02502<02C02J02O02P02Q02R02S02T02U02Y02]02i03503<03=03>03?03@03A03B03I03P03W03[03b03g03n03o04:04?04J04Q04R04V04Z04^04e04f04g04k05205305:05;05<05C05U05V05W05^05f05n06:06F06M06N06O06S06W06[06c06n07507:07A07H07O07V07]07^07e07l08308:08;08<08=08D08H08L08S08^08i09409?09@09G09L09Q09V09]09b09i0:00:;0:C0:M0:R0:]0:h0:i0;00;10;80;<0;@0;D0;H0;O0;S0;Z0;a0;h0;o0<;0<B0<M0<T0<U0<\0<n0=20=70=;S2KH2LOS2KH2LOS2KH2LO3SHRS2KH2LOSS2KH2LOSSS2HBS2KH2LOS2KH2LOSS2KH2LOSS2LOS2LOS2KH2LOS2HBS2KH2LOS2KH2LOS2KH2LOS2KH2LOFS2KH2LOSSS2KH2LOS2KH2LOS2KH2LOS2KH2LOS3RSPSSSSSSS2LOS2LOS2SZ3LOW3HIES2SZ3LOW3HIES2KH2LOSSSSSSS2KH2LOS2KH2LOS2KH2LOS2HBS2KH2LOS3RSPS2KH2LOSS2KH2LO3SHRS3RSPS2KH2LO3SHRS2KH2LOSS2LOS2LOS2LOS2KH2LOSSS2HBS2KH2LOSS2KH2LOSSS2KH2LOS2AL2SL2SZ3LOW3HIESSS2KH2LOS3LOW2K2S3LOW2K2S2SZ3LOW3HIES2SZ3LOW3HIES2KH2LOSSS2LOS2LOS2LOS2KH3SHRS2KH2LO3SHRS2KH2LOS3RSPS2KH2LOS2KH2LOS2KH2LOS2KH2LOS2KH2LOSS2KH2LOS2KH2LOS2KH2LOS2KH2LOSSFS2KH2LOS2LOS2LOS2KH2LOS5SMALL3SHRS5SMALL3SHRS5SMALL3SHRS2KH2LO3SHRSS2KH2LOS3RSPS3SHRS3SHRS2KH2LOS3RSPS2KH2LOS2KH2LOS2SZ3HIE2K2S3HIE2K9S5SMALL2KTS3K10S2KH2LO3SHRS2KH2LO3SHRSS2KH2LOSS2KH2LOS2LOS2LOS2LOS2LOS2KH2LOS2HBS2KH2LOS2KH2LOS2KH2LOS2KH2LOS2SZ3LOW3HIES2KH2LOS2KH2LO3SHRS2KH2LOSS2KH2LOS2AL2SL2SZ3LOW3HIES2HBS3RSPS2HB".
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
  pose proof (rw_cells_transport bsegs _ _ _ _ _ FR MU2 WM2 ltac:(cbn [disjoint_from cells_size csize]; lia)) as FR'.
  pose proof (stk_transport_disjoint bsegs _ _ _ _ _ ST MU2 WM2 ltac:(cbn [disjoint_from]; lia)) as ST'.
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
    ms' = MS (mkR (Z_to_bv 64 0x3f288) (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 (Z_to_bv 64 0x132b68) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 2) (Z_to_bv 64 0x1b21d) (Z_to_bv 64 d) s5 s6 (Z_to_bv 64 0x9ae98) s8 (Z_to_bv 64 0x9e838)
                  (Z_to_bv 64 0xa1038) s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x3f288) fc None m' (seg_rom bsegs)
    /\ munch [(sb, sb + sl)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' sb [CB (Z.to_nat sl) (repeat (Z_to_bv 8 0) (Z.to_nat sl))].

#[using="Type"] Lemma unreg_one_spec : forall RNG (sb sl : Z) (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s8 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem) (spv d beg swr : Z) (gsz gnm gmd gdy glc godr : word) (junk : list byte),
  mem_inv bsegs m -> mdtor_rt m ->
  rw_cells bsegs m d [C8 (Z_to_bv 64 beg); C8 gsz; C8 (Z_to_bv 64 swr); C8 gnm; C8 gmd; C8 gdy; C8 glc; C8 godr] ->
  rw_cells bsegs m (d + 16) [C1 (Z_to_bv 8 swr)] ->
  beg mod 8 = 0 -> swr mod 8 = 0 -> 0 < swr < 256 -> 0x10000 <= beg -> beg + swr <= 0x5f6000 ->
  0x10000 <= d -> d + 64 <= 0x5f6000 -> 0 <= spv < 2^64 ->
  sb = shd beg -> sl = shn swr ->
  rw_cells bsegs m sb [CB (Z.to_nat sl) junk] ->
  rng_aimg RNG -> rng RNG sb sl ->
  evtF bsegs RNG (unreg_one_post spv d sb sl gp tp s5 s6 s8 s11 F fc m)
    (MS (mkR ra (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 (Z_to_bv 64 0x132b68) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 2) (Z_to_bv 64 0x1b21d) (Z_to_bv 64 d) s5 s6 (Z_to_bv 64 0x9ae98) s8 (Z_to_bv 64 0x9e838)
             (Z_to_bv 64 0xa1038) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3f2a0) fc None m (seg_rom bsegs)).
Proof.
  intros until junk. intros MI RT D DB AL SL SWR LOW HIE DLO DHI SPV -> -> DST RIMG RSH.
  pose proof RT as RT'. destruct RT' as (PGC & GOT & GOT80 & REAL & SHB & INI & CANP & THR & RGL).
  pose proof (munch_refl [(shd beg, shd beg + shn swr)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (SHR : 0x7fffa000 <= shd beg /\ shd beg + shn swr <= 0x800cd000 /\ 0 < shn swr < 32).
  { unfold shd, shn, SHOFF. Local Ltac2 Set LiaHints.tbl := fun () => "00\0>10009457963.7710009457963.8014346694262.7519620497065.8024115025141.8024982578487.6824982578614.6926082619952.7728913119920.8029001722024.7629001722024.7929071941542.8229601281241.6829784416347.6829784416474.6929784612193.6529786758908.6930422568588.7030424711306.7030426549930.8933161241475.7835499809676.6936350900204.6937728604022.7840703222448.8941209397009.7941983118326.7248107158204.8948109515932.7051563130523.8152076332688.7452076332702.7653510313876.7755047472860.7859308628433.6759308632823.7059588178608.8059702520969.6560996812196.8163674995624.7563677092781.8263683735724.6764713536689.7664713536689.7900000100200300400500600700D00E00F00G00H00M00N00O00P00Q00V00[00`00a00b01501601701801901>01C01D01E01F01G01P01\01d01e02802A02I02Q02^02g030SSSFFSSS3SWR3LOW3HIESFFFS3SWRSSSSS3SHRS3SHRS3SHRFSS2AL2SL3SWR3LOW3HIESSSSS3SHRS3SHRFFFSS3DLO3DHIS3SWR3HIE2K2S3SHR2KTSS2AL2SL3SWR3LOW3HIES3DLO3DHIS3LOW2K2S3LOW2K2S3SWR3LOW3HIES3DLO3DHIS3DLO3DHI".
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
  replace (ret_pc (Z_to_bv 64 0x3f288)) with (Z_to_bv 64 0x3f288 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
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
     rw_cells bsegs m d [C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 sz); C8 (Z_to_bv 64 swr); C8 (Z_to_bv 64 nm); C8 (Z_to_bv 64 md);
                         C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 odr)]
  /\ rw_cells bsegs m (d + 16) [C1 (Z_to_bv 8 swr)].

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
  | (b, sz, swr, nm, md) :: G' => (exists j, rw_cells bsegs m (shd b) [CB (Z.to_nat (shn swr)) j]) /\ gshads m G'
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
  Local Ltac2 Set LiaHints.tbl := fun () => "0010>29608132959.19000001F".
repeat split; try assumption; try lia. apply IH. exact H9.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma AGLOBALS_sorted : gsorted 0x7fffc1a8 0x7fffc1b8 AGLOBALS.
Proof. apply gsortedb_ok. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma AGLOBALS_length : Z.of_nat (length AGLOBALS) = 2.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma cb_sub : forall m a (k : nat) j a' n', rw_cells bsegs m a [CB k j] -> a <= a' -> 0 <= n' -> a' + n' <= a + Z.of_nat k ->
  exists j', rw_cells bsegs m a' [CB (Z.to_nat n') j'].
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

#[using="Type"] Lemma gshads_of_hull : forall G lo hi m a (k : nat) j, rw_cells bsegs m a [CB k j] -> a <= lo -> hi <= a + Z.of_nat k ->
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

#[using="Type"] Lemma gdescs_transport : forall G W m m' d, gdescs m d G -> munch W m m' -> wmono bsegs m m' ->
  (forall A n, d <= A -> 0 <= n -> A + n <= d + 64 * Z.of_nat (length G) -> disjoint_from W A n) -> gdescs m' d G.
Proof.
  induction G as [|[[[[b sz] swr] nm] md] G IH]; intros W m m' d HG MU WM HD; cbn [gdescs length] in *; [exact I|].
  destruct HG as [[D1 D2] HG]. split; [split|].
  - Local Ltac2 Set LiaHints.tbl := fun () => "0090>12128333532.1817451922806.182424953317.23 28082131295.183080755707.23 33669200788.1841912482204.2346585200585.1868059072559.1800000100200600700;00<00@00A00BSSS2H2SS2H3SS2H1SS".
eapply rw_cells_transport; [exact D1| exact MU| exact WM| apply HD; cbn [cells_size csize Nat.add]; lia].
  - eapply rw_cells_transport; [exact D2| exact MU| exact WM| apply HD; cbn [cells_size csize Nat.add]; lia].
  - eapply IH; [exact HG| exact MU| exact WM|]. intros A n H1 H2 H3. apply HD; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma gshads_transport : forall G W m m' lo hi, gshads m G -> gsorted lo hi G -> munch W m m' -> wmono bsegs m m' ->
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
  /\ rw_cells bsegs m 0x99cb0 [C8 (Z_to_bv 64 0x9d8e0); C8 (Z_to_bv 64 0x9d960)]     (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x9d980 [C8 (Z_to_bv 64 1)]                                     (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x9e8f0 [C8 (Z_to_bv 64 0)]                                     (* [comment removed for export] *)
  /\ gdescs m 0x9d8e0 AGLOBALS                                                        (* [comment removed for export] *)
  /\ (exists j, rw_cells bsegs m 0x7fffc1a8 [CB 16 j])                               (* [comment removed for export] *)
  /\ (exists j, rw_cells bsegs m 0x8000bb1c [CB 16 j]).                              (* [comment removed for export] *)

#[using="Type"] Lemma mdtor_pre_frame : forall sp m m',
  mdtor_pre m -> KHIGH <= sp - 48 - MDTOR_DEPTH -> munch (AEXIT_W1 sp) m m' -> wmono bsegs m m' -> mdtor_pre m'.
Proof.
  intros sp m m' P KH MU WM. unfold KHIGH, MDTOR_DEPTH in KH.
  assert (D : forall A n, 0 <= n -> A + n <= 0x80014048 -> 0x5f4244 <= A \/ (0x9d9d1 <= A /\ A + n <= 0x5f4020) \/ A + n <= 0x9d9d0 ->
              disjoint_from (AEXIT_W1 sp) A n).
  { intros A n Hn HA HO. unfold AEXIT_W1, MDTOR_DEPTH. cbn. Local Ltac2 Set LiaHints.tbl := fun () => "00E0>1464927763.18 16521559870.1817360099379.1817653767325.1719151096254.1822552125012.172424953317.23 24897347646.1827036457245.1728337422245.1329258167091.183115850481.23 33670935481.1835219105309.1737118387390.1837274686183.2344984833565.1753051163293.1754427116979.1857449916702.1863555565235.1800000100200300400500900=00>00?00I00J00N00O00P00Q00U00V00W00X00Y00ZSSSSSS2KHS2H2SSS2KH2HA2HOSS2H3SSSS2H3SSSSS".
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
  intros lo hi a b m m1 m' M1 M2 H H'. eapply munch_trans; [eapply munch_weaken; [| exact M1] | eapply munch_weaken; [| exact M2]];
    unfold sub_fp; intros x Hx; cbn [outside] in *; destruct Hx as [Hx _]; split; try exact I; lia.
Qed.

#[using="Type"] Lemma unreg_loop : forall G RNG (lo hi d spv : Z) (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s8 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem),
  G <> [] ->
  mem_inv bsegs m -> mdtor_rt m -> gdescs m d G -> gshads m G -> gsorted lo hi G ->
  0x10000 <= d -> d + 64 * Z.of_nat (length G) <= 0x5f6000 -> 0x7fffa000 <= lo -> hi <= 0x800cd000 -> 0 <= spv < 2^64 ->
  rng_aimg RNG -> rng RNG lo (hi - lo) ->
  evtF bsegs RNG (fun ms' => exists (ra' t0' t1' t2' s0' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
      ms' = MS (mkR ra' (Z_to_bv 64 spv) gp tp t0' t1' t2' s0' (Z_to_bv 64 0x132b68) a0' a1' a2' a3' a4' a5' a6' a7'
                    (Z_to_bv 64 2) (Z_to_bv 64 0x1b21d) (Z_to_bv 64 (d + 64 * Z.of_nat (length G))) s5 s6 (Z_to_bv 64 0x9ae98) s8
                    (Z_to_bv 64 0x9e838) (Z_to_bv 64 0xa1038) (Z_to_bv 64 0) t3' t4' t5' t6')
               F (Z_to_bv 64 0x3f4a4) fc None m' (seg_rom bsegs)
      /\ munch [(lo, hi)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m')
    (MS (mkR ra (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 (Z_to_bv 64 0x132b68) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 2) (Z_to_bv 64 0x1b21d) (Z_to_bv 64 d) s5 s6 (Z_to_bv 64 0x9ae98) s8 (Z_to_bv 64 0x9e838)
             (Z_to_bv 64 0xa1038) (Z_to_bv 64 (Z.of_nat (length G))) t3 t4 t5 t6)
        F (Z_to_bv 64 0x3f2a0) fc None m (seg_rom bsegs)).
Proof.
  induction G as [|[[[[b sz] swr] nm] md] G IH]; intros until m; intros NE MI RT HD HS HSO D0 D1 LO HI SPV RIMG RH; [congruence|].
  clear NE. cbn [gdescs gshads length] in *. pose proof HSO as HSO'. cbn [gsorted] in HSO'.
  destruct HD as [[DC DB] HD]. destruct HS as [[j SH] HS]. destruct HSO' as (L1 & L2 & AL & SL & SW & BL & BH & HSO').
  rewrite Nat2Z.inj_succ in D1 |- *.
  pose proof (Zle_0_nat (length G)) as LG.
  Local Ltac2 Set LiaHints.tbl := fun () => "00X0?11150279611.66 14892681432.96 15306844775.96 15873449912.93 15877545095.11718375735985.90 19301059053.96 21817279323.88 22063674542.66 2424953317.94  2728801115.66  27616505739.66 29603282131.66 29784530535.63 30090030831.96 30096696442.66 33669004442.87 33935627387.66 34506992316.87 35253210252.96 37431855784.66 37529455908.93 38610020951.95 44200493303.93 44204786632.11747404309994.11747988827160.64 48464177354.95 48701252342.96 52061149739.94 52293735510.63 54612051697.94 54917223859.10257829424363.65 59709448941.11762512989918.11766110553915.10267770632493.1027501253514.93  7853444906.96  00000700;00B00F00J00T00U00\00`00d00h00l01001101601;01<01@01G01K01O01P01T01X01\01]01d01g02102;02B02I02J02Q02R02Y02Z02d02g02kS2D12LGS2D1S2L12N0S2L1S2L1S2LO2L12HASS2N02SBS2D0S2H2S2ALS2SLS2SWSS3SPVS3SPVSS2BHS2D12LGS2D0S2BLFS2H1S2L2S2L2SS2LO2L1S1KS2LO2L12N0S2D02D12LGS2SL2SWS2D12H3FS2L12L2SS2L12N0FS2D02D12LGS1KS2HI".
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
  pose proof (rw_cells_transport bsegs _ _ _ _ _ DC MU1 WM1 ltac:(apply DJ; cbn [cells_size csize Nat.add]; lia)) as DC1.
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
  pose proof (munch_refl [(bv_unsigned sp - 1024, bv_unsigned sp); (0x9d980, 0x9d988); (0x9e8f0, 0x9e8f8);
              (0x7fffc1a8, 0x7fffc1b8); (0x8000bb1c, 0x8000bb2c)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  (* [comment removed for export] *)
  Local Ltac2 Set LiaHints.tbl := fun () => "0:<0?10088628586.12110188553603.87 10263306008.90 10427110936.90 10560830360.90 10644388632.91 10685224615.89 10807678616.90 11013911192.90 11362458803.90 11475581208.92 11508929048.90 11633885848.90 11752361332.11211752361332.83 11939284504.84 11939284504.87 11939284504.94 11972186776.90 1199623832.90  1215257368.92  12237445648.102123561496.90   12428150072.11612551814168.90 12751175960.92 12762061292.88 12776239640.90 12796337816.90 12797919724.88 13000380547.11813000380547.89 13092900324.86 13451212952.90 13651810739.87 13651810739.94 1371286659.115 1371286659.86  13730566004.11213730566004.83 1384849688.84  1384849688.87  1384849688.94  13949724851.91 14008773748.11914201179716.79 14222997272.89 14224430925.10814377232691.90 14386403300.86 14386403301.11614404687680.88 14726028739.11714921199539.90 14980397443.11714980397443.87 15026383640.91 15045052203.90 15074360607.10215151340440.90 15169268888.94 15500139544.91 15670301260.86 15741785496.91 15765949812.11215765949812.83 15957830552.90 16213386675.92 16354217752.91 16528340147.89 16641156659.90 16790362008.90 16897753792.88 16955585843.90 17400065396.11217400065396.83 17499552691.91 17730680088.91 17753146207.1021776774040.90  17811835032.92 1792101400.91  17927060531.90 18167079320.94 18208632856.92 18260999576.90 18265732580.11418265732580.84 18359819160.90 18618292611.12318618292611.91 18697587807.10218792264115.92 18813191192.84 18813191192.87 18813191192.94 18820901016.90 19006120615.84 19042827563.91 19066511015.89 19145457048.90 19208070823.87 19219771955.90 1933448932.115 1933448932.86  19365792884.11919482963480.91 19493191704.92 19619045547.89 19630331032.90 19666379416.90 19772541407.10219789258868.11919977582360.92 19992479000.92 20049970968.89 20084426675.89 20210087832.90 20406904000.90 20433961190.74 20514293811.90 20514546292.11920622842136.90 20667246060.88 20805123751.87 21207973122.10821541434755.11621541434755.87 2156398744.90  21612304792.90 21781323315.90 21797470616.89 21830222104.92 22067993779.92 22143267480.90 22193440237.10722227798296.92 22252640536.92 22328128792.92 22380394776.91 22519161511.87 22551103139.11722931427392.88 23052457452.88 23077509607.87 23192247704.90 23259527847.86 23360180915.90 2351266880.88  23706670360.92 23790048051.94 23891548451.11724184843160.90 24426826008.92 24452376600.92 24616866328.90 24646346931.91 24651604632.90 25073854771.90 25076071819.11725233675160.90 25355543319.80 25382382360.91 25435258127.11525435258127.85 25482792915.79 25566553219.11425566553219.84 25624113075.92 25785063811.11725785063811.87 25939066547.91 26314001944.91 26368409395.90 26383672600.91 26424324672.88 26523703576.91 27147338155.93 27233612979.92 27439898422.98 27442097076.81 27482220312.90 2749330817.121 27617184920.90 27620275190.11427661120819.90 27681188262.77 27718319512.90 27734079512.90 28072922155.89 28202990515.91 28524776856.90 28630498355.90 28913119921.12128923164140.88 28928117555.90 28947464871.88 28950691264.88 29028832419.11729142842027.89 29371901571.10329371901571.89 29381286040.90 29388426264.92 29714896536.90 29737833181.12129823858968.84 29823858968.87 29823858968.94 2999309167.112 2999309167.83  30009181720.90 30051503896.92 30085204460.88 30090674789.10230090674794.88 30093845803.91 30189236903.91 30223226776.90 30457115928.92 30789699507.92 30995698343.87 3103202328.91  3105926367.102 31160703967.10231161366443.89 31217207347.90 31229223704.91 31399093385.10531470099167.10231562805016.90 31793241204.11931864790296.90 31872754072.90 32090383583.10232227944728.84 32227944728.87 32227944728.94 32460070848.90 32514805272.91 32596943000.90 3260688280.90  32614775744.82 32656438424.90 32709175007.10232985609624.90 33008100632.91 3336609688.90  33400476056.90 33510003693.10633663610520.94 33694390168.90 33764744995.11733969037336.92 33971183717.87 33971183723.11833994825496.90 34109661676.88 34330576408.89 34388506392.90 34498180888.90 34894844291.10234894844291.87 34949774985.11834951301952.88 34999993796.77 35514450401.98 35565964824.92 35639914264.90 35791044212.11935920075244.88 36213580312.90 36243838616.90 36444003871.10236574674563.11936574674563.88 36606830211.11936606830211.89 36809482264.89 37116806296.90 37238554472.90 37245778797.1083724717791.102 37247578328.77 37247578331.79 37247661040.10837247661040.79 37263307375.11937314855832.84 37314855832.87 37314855832.94 37504724647.91 37623256436.11237623256436.83 37728118936.90 378738307.87   37925612696.90 38042474520.90 3806088728.90  38061727256.90 38139299188.11238139299188.83 38172936619.89 38206039448.94 3830064277.106 38479588672.88 38689803288.92 38880710680.91 38903003800.90 39073975183.94 39123711019.88 39242478692.86 3938769889.122 39408141080.92 3940867048.90  39563569944.91 3962756376.92  39941648665.10740046219415.71 40158618216.12140243014947.11740540307045.87 40540307050.11740636537073.11040636537073.81 40970295488.89 410810228.83   41117850981.87 41117850986.11741144390296.90 41387607192.94 4142759704.90  41699223960.90 41789215768.91 41904973208.90 42367474456.91 42495348204.88 42600342424.90 42705453464.90 42761554328.90 42766495640.90 42805740039.11642925336273.11743061379371.72 43085085208.91 43121191467.91 43122952810.88 43122952811.11843189011864.90 43245169304.90 43378675608.92 43507384707.11643507384707.87 43543063576.91 44195277809.11744420783207.11344420783207.83 44450003224.92 44583025012.11944624256280.84 44624256280.87 44624256280.94 4466241176.90  44902756248.90 44926648472.90 44964803431.11244964803431.80 45093806515.90 45095562520.84 45095562520.87 45095562520.94 4545862040.94  45487759923.94 45580174360.92 46386664472.92 46390321508.86 46392837507.11746392837507.87 46408956396.88 46430889452.88 46587431704.91 46700966040.90 46873852568.91 46894613144.90 47006590528.88 47151234968.90 47153760152.90 47202336408.94 47234531096.90 47235946392.90 47353775455.10247562253592.92 47670797848.94 47678950835.91 47688149866.11747688149866.88 47900152984.94 47945789336.90 48075001395.90 48268756632.90 48337895576.92 48562591384.94 4876052416.92  4887167092.119 48912292248.90 48943411864.90 49065514264.92 49317635608.92 49345969283.87 49463278104.91 49705919860.11249705919860.83 49951849624.90 50033228952.90 50120722712.92 50269882218.11750269882218.88 5029682584.90  50305698327.88 50430425496.90 5054248984.90  50601973784.84 50601973784.87 50601973784.94 50628435992.91 50653354547.90 50664164139.89 50686839192.90 5072571819.89  50753392792.94 50771321240.90 51234361003.89 51270112152.90 51284503704.90 51430120600.90 51567446375.11451567446375.85 51693436583.87 5170374848.85  52076332701.11952138178584.92 52151318827.90 52294831256.90 52357093784.90 52553219883.94 52577538839.11252577538839.11952577538839.83 52577538839.84 52577538839.87 52577538839.88 52577538839.89 52577538839.90 52577538839.91 52577538839.92 52577538839.94 52610616088.91 52615423000.91 52731493528.90 52931482264.90 52994023284.11252994023284.83 53032137664.90 53113023478.11253322291235.11753510313876.11653596280713.11153596280713.82 5368629927.88  53729025688.90 53818677656.90 53845887512.84 53845887512.87 53845887512.94 53971039640.90 54024088963.87 54140369575.87 54164510851.11354164510851.81 54401715352.91 54425058712.90 54457725208.92 54509322919.87 54775059736.92 54907835544.90 54959380579.11754989085996.88 55177897240.92 55238157483.89 55372791924.11955401790488.92 55496111076.10155606215043.11655606215043.87 55632076824.89 55654128664.92 55790008216.90 55812115608.90 5603900824.90  56170414366.94 561775768.90   56244589464.90 56524740032.87 56604514840.91 56746208792.90 56751191832.89 56908737432.90 56964914855.89 57057137432.91 57284671128.90 57387588263.87 57447876248.94 57480980335.11257480980335.83 57766271107.91 57915518083.11857915518083.88 57953326616.92 57956650648.94 58108299800.92 58135773316.75 58459745811.80 58752742260.11258752742260.83 59005288815.11959051098432.88 59178106163.85 59588178609.12159798679832.84 59798679832.87 59798679832.94 6014957611.90  60290486879.10260476074136.90 60566080628.11960592077428.11960647885491.94 60835735704.90 61042781208.91 61262187744.77 61262187747.79 61336055832.91 61453465240.90 61489225752.89 61542075584.90 61592356519.88 6177131892.112 6177131892.83  61926639340.88 61959141144.89 62316770328.92 62498388504.92 62549928615.87 62560510784.88 62579896600.84 62579896600.87 62579896600.94 62856691096.90 62921323032.92 62991541526.11263226762931.92 63620716339.90 63817845272.91 639945956.115  639945956.86   64051252632.90 64189933208.90 64241034648.90 64261731243.89 6446145560.92  64505296280.94 64552605464.89 64666959615.10164868927256.90 64955147683.11764981789848.90 65051750080.89 65115206040.90 65212743211.83 65212743211.86 65212743211.93 65281083544.90 65316957080.90 65508437732.10165508437732.86 65530800136.10865567805059.11865567805059.88 65640642840.90 65647300376.89 65661944856.92 65788601011.92 65958160408.90 66093525016.92 6615494311.89  66215846707.90 66288125208.90 66349738136.90 6638482584.90  66599062040.91 66716352803.11766721159227.84 66772627111.87 66806001892.86 66842326680.90 66959188504.84 66959188504.87 66959188504.94 67081926311.81 67130952472.91 67136312999.87 67157832433.12167168426264.92 67445091224.90 67578108480.92 67769248536.90 67803480856.91 6790368152.92  68036888216.90 68037925795.11768094715463.77 6816007130.94  68162666607.11268162666607.83 68334534168.91 68610161176.89 68703532440.90 6931027736.89  7032139380.112 7032139380.83  7238556388.115 7238556388.86  7456383000.92  7502079531.91  7786772964.86  7786772965.116 7835469603.117 800955800.90   8128395288.92  83611443.90    8387529152.89  8460265368.90  8566170392.90  8600740120.92  8603416747.89  9080374244.86  9080374245.116 9320669208.92  9791719555.118 9791719555.89  9969733400.90  9972757016.90  00000100200:00B00J00R00S00[00c00d00l01401<01=01>01F01N01V01^01f01n01o02702802@02H02P02X02`02h02i02j02k03303403503603703803903A03I03Q03R03S03T03\03]03^03_03`03d03e03f03g03h04004504=04E04M04U04Y04a04b04c04k04l05405505605>05B05C05D05E05F05N05O05W05_05g05h06006806@06A06B06J06K06L06M06N06V06^06f06n06o07407507=07>07?07@07A07B07J07R07W07_07g07h07i08108908A08B08J08N08O08P08Q08Y08a08b08c08d08e08m09509609>09F09G09O09P09X09`09h0:00:10:=0:A0:I0:N0:V0:W0:X0:\0:d0:e0;10;90;A0;I0;Q0;R0;Z0;[0;g0;o0<00<80<90<:0<;0<<0<=0<>0<?0<@0<A0<I0<J0<R0<V0<^0<c0<d0=20=>0=F0=G0=O0=P0=Q0=U0=]0=e0=j0=k0>30>40>50>=0>>0>?0>C0>O0>T0>U0>V0>^0>f0>n0>o0?70??0?G0?O0?W0?_0?g0?o0@00@10@60@70@?0@G0@H0@I0@Q0@R0@S0@X0@Y0@a0@b0@c0@k0@l0A40A<0A=0AE0AM0AU0AY0Aa0Ai0B10B50B=0B>0BF0BN0BV0B^0B_0Bg0Bo0C;0CC0CD0CE0CM0CU0C]0Ce0Cm0Cn0Co0D00D40D50D60D>0DF0DG0DO0DW0D_0D`0Da0Db0Dc0Dd0Dl0E40E50E60E70E80E90E:0E;0EC0EK0ES0E[0E\0E]0E^0Ef0Eg0Eo0F70F?0FG0FH0FI0FN0FV0FZ0F^0Ff0Fn0G60G70G<0G=0G>0GF0GG0GO0GW0G[0G_0G`0Gl0Gm0Gn0Go0H00H40H50H60H70H?0HG0HO0HW0H_0Hg0Ho0I70I?0IG0IO0IW0IX0Id0Ih0J00J50J60J70J?0JG0JO0JP0JQ0JY0JZ0J[0J\0Jd0Je0Jm0K50K=0KE0KM0KU0KV0KW0KX0K`0Kh0L00L80L90LA0LI0LJ0LK0LL0LT0L\0Ld0Ll0M40M<0M@0MH0MP0MX0M`0Mh0Mi0N10N90N:0N;0N<0N@0NH0NI0NQ0NY0Na0Ne0Nf0Nn0O60O>0OF0OG0OO0OP0OQ0OY0Oa0Oi0Oj0Ok0P30P40P<0PD0PL0PT0P\0Pd0Pe0Pj0Q20Q70Q?0QG0QL0QT0Q\0Qd0Qe0Qf0Qg0Qk0Ql0R40R90RA0RI0RJ0RK0RL0RM0RN0RO0RP0RQ0RR0RS0RT0RU0R]0Re0Rm0S50S60S70S;0S<0SH0SI0SJ0SK0SL0ST0S\0Sd0Sl0T40T<0T=0T>0T?0T@0TH0TP0TX0TY0Ta0Ti0U50U=0UE0UJ0UK0US0UX0UY0UZ0Ub0Uj0V20V:0VB0VC0VK0VS0VW0V_0Vg0Vo0W70W80W@0WH0WI0WQ0WY0Wa0Wb0Wc0Wd0Wl0X40X<0X@0XA0XB0XC0XK0XO0XP0XQ0XY0Xa0Xi0Xn0Xo0Y70Y80Y90Y:0YB0YJ0YK0YL0YT0Y\0Yd0Yh0Yi0Yj0Yk0Z30Z;0ZC0ZK0ZL0ZP0ZX0Z`0Zh0[00[80[90[:0[;0[C0[D0[E0[M0[U0[]0[b0[j0\20\:0\;0\C0\O0\W0\[0\c0\h0\m0]20]:0]B0]C0]D0]H0]I0]J0]R0]Z0]b0]c0]k0^30^40^50^=0^E0^M0^U0^a0^l0^m0^n0_60_>0_F0_N0_O0_W0_X0_Y0_a0_i0_m0`50`=0`E0`M0`Y0`Z0`[0`c0`k0a30a;0aC0aK0aL0aM0aN0aO0aW0a\0a]0a^0aj0b20b:0b;0b?0bG0bO0bW0b\0b]0b^0bf0bg0bh0c00c8SSS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'SS2LO3KH'S2LO3KH'SS2LO3KH'S2LO3KH'S2LO3KH'SSS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'FS2LO3KH'FS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'SSSS2LO3KH'SSSSSSS2LO3KH'S2LO3KH'S2LO3KH'SSSS2LO3KH'FSSSS2HBFSSSS2LO3KH'S3RSPS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2HBS2LO3KH'SSS2LO3KH'SS2LO3KH'SSS2LO3KH'S2HBSSSSS2LO3KH'SS2LO3KH'S2LO3KH'S2LO3KH'SS2LO3KH'S2LO3KH'S2LO3KH'SSS2LO3KH'SSSSS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'SS3RSPSS2LO3KH'SSSSSS2LO3KH'S2LO3KH'S3RSPS2LO3KH'S2LO3KH'FSS2LO3KH'S2LO3KH'S2LO3KH'SS2LO3KH'S2HBSSSS2LO3KH'S2LO3KH'SFSSS2LO3KH'S2LO3KH'SS2LO3KH'S2LO3KH'SS2LO3KH'SS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'SS2LO3KH'3HspS2HBS2LO3KH'S3RSPS2LO3KH'SSS2HBS2LO3KH'SS2LO3KH'3HspS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'SS2LO3KH'SS2LO3KH'3HspS2LO3KH'SS2LO3KH'SSFSSSSSSS2LO3KH'SS2LO3KH'S2HBS2LO3KH'S3RSPSS2LO3KH'3RSP1HS2LO3KH'3RSPS2LO3KH'FS2LO3KH'SSS2LOS2LO3KH'S2LO3KH'S3RSPSS2LO3KH'SSS2LO3KH'SSS2HBS2LO3KH'3HspS3RSPSSS2LO3KH'S2LO3KH'S2LO3KH'FS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'SSS3RSPSS2LO3KH'S2LO3KH'SSS2LO3KH'SSS3RSPSS2LO3KH'SSS2LO3KH'SS2LO3KH'S2LO3KH'SS2LO3KH'S2LO3KH'S2LO3KH'S2HBS2LO3KH'S2LO3KH'S2LO3KH'S2HBS2LO3KH'SS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'SS2LO3KH'S2LO3KH'S2LO3KH'3HspS2LO3KH'SSS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'SSSS2HBFFS2LO3KH'S2LO3KH'SS2LO3KH'S2LO3KH'S2LO3KH'SSSSSS2LO3KH'S2LO3KH'SFSFFFFS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'SSSS2LO3KH'SS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'SSS3RSPS2LO3KH'S2LOS2HBS2LO3KH'S2LO3KH'S2LO3KH'SS3RSPSSS2LO3KH'SS2LO3KH'S2LO3KH'S2LOS2LOSS2LO3KH'3HspSSSSS2HBSSSS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'FS2LO3KH'3HspS2LOS2LO3KH'S3RSPSSS2LO3KH'S2LO3KH'S2LO3KH'SSS2LO3KH'SSSS2LO3KH'SS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'SSSS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'SS2LO3KH'S2LO3KH'SSSS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2HBS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'SS2LO3KH'S2LO3KH'SSSS2LOS2LO3KH'SS2LO3KH'S2LO3KH'S2LO3KH'S2HBSS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'SS2LO3KH'SSS2LO3KH'S2LO3KH'S2LO3KH'SSS2LO3KH'SS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'SS3RSPS2LO3KH'S3RSPS2LO3KH'S2LO3KH'S3RSPS2LO3KH'S2LO3KH'S2LO3KH'SSSS2HBFS2LO3KH'S3RSPS2LO3KH'S2LO3KH'SSSSSSSSSSSSS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'SSS2HBSS2LO3KH'3HspSSSSS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'SSSSS2LO3KH'S2LO3KH'S2LO3KH'SS2LO3KH'S2LO3KH'S2LO3KH'3HspS2LO3KH'S2LO3KH'S3RSPSS2LO3KH'S3KH'SSS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'SS2LO3KH'S2LO3KH'S2HBS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'SS2LO3KH'S2LO3KH'SS2LO3KH'S2LO3KH'S2LO3KH'SSSS2LO3KH'S2LO3KH'S2LO3KH'S2LOSSSS2LO3KH'S2HBSSS2LO3KH'S2LO3KH'S2LO3KH'S3RSPSS2LO3KH'SSSS2LO3KH'S2LO3KH'FFS2LO3KH'S2LO3KH'S2LO3KH'S2HBSSSS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'SS2HBS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'SSSS2LO3KH'SSS2LO3KH'S2LO3KH'S2LO3KH'S3RSPS2LO3KH'S2LO3KH'S2LO3KH'SS2LO3KH'S2LO3KH'3HspS2LO3KH'S2HBS2LO3KH'S3RSPS3RSPS3RSPS2LO3KH'S2LO3KH'SSS2LOSSS2LO3KH'S2LO3KH'S2LO3KH'SS2LO3KH'S2LO3KH'SSS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'3HspS2LO3KH'2H3SSS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'SS2LO3KH'SSS2LO3KH'S2LO3KH'S2HBS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'3HspSSS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'SSSSS2LO3KH'S3RSPSSS2LO3KH'3HspS2LO3KH'S2LO3KH'SS2HBS2LO3KH'S2LO3KH'S2LO3KH'S3RSPSSS2LO3KH'SSS2LO3KH'S2LO3KH'".
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
  steps_to 0x3f18c%Z.
  amo_step. astep. amo_step. astep. astep.
  move MTX after RGL.                                  (* [comment removed for export] *)
  (* [comment removed for export] *)
  hstep. hstep. astep.
  steps_to 0x3f2a0%Z.
  (* [comment removed for export] *)
  lazymatch goal with M : munch _ m ?mc, W : wmono _ m ?mc |- _ =>
    assert (GD' : gdescs mc 0x9d8e0 AGLOBALS)
      by (eapply gdescs_transport; [exact GD| exact M| exact W| rewrite AGLOBALS_length; intros A n H1 H2 H3; cbn [disjoint_from]; lia]) end.
  assert (HS : gshads _ AGLOBALS) by (eapply (gshads_of_hull AGLOBALS 0x7fffc1a8 0x7fffc1b8); [exact S1| lia| lia| exact AGLOBALS_sorted]).
  replace (Z_to_bv 64 2) with (Z_to_bv 64 (Z.of_nat (length AGLOBALS))) by reflexivity.
  move RW2 at bottom.
  call (unreg_loop AGLOBALS RNG 0x7fffc1a8 0x7fffc1b8 0x9d8e0).
  all: first [ unfold AGLOBALS; discriminate | exact GD' | exact HS | exact AGLOBALS_sorted | rewrite AGLOBALS_length; lia | side RIMG RSTK KH ].
  clear RW2 GD GD' HS.
  rewrite AGLOBALS_length.
  (* [comment removed for export] *)
  do 6 hstep. hstep.
  move RW3 at bottom.
  call_sp (poison_low_spec RNG 0x8000bb1c 16). all: side RIMG RSTK KH. clear RW3.
  lit_nat.
  (* [comment removed for export] *)
  steps_to 0x3f4fc%Z.
  amo_step. astep. amo_step. astep. astep.
  astep.                                               (* [comment removed for export] *)
  steps_to 0x3f754%Z.
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