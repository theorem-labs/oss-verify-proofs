(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem Fpu.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_ExpfModelB () := "K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01c69OSSVerify5KrLib2K53Lib:ExpfModelB8bil_cellC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
(* [comment removed for export] *)
Definition v_add (x y : word) : word := Z_to_bv 64 (bv_unsigned x + bv_unsigned y).
Definition v_andi (x : word) (imm : Z) : word := Z_to_bv 64 (Z.land (bv_unsigned x) (bv_wrap 64 imm)).
Definition c_eq (x y : word) : bool := bv_eqb x y.
Definition c_ltu (x y : word) : bool := bv_ltu x y.
Definition v_slli (x : word) (sh : Z) : word := Z_to_bv 64 (Z.shiftl (bv_unsigned x) sh).
Definition v_srli (x : word) (sh : Z) : word := Z_to_bv 64 (Z.shiftr (bv_unsigned x) sh).

Definition ES : format := fp_format FMT_S.
Definition ED : format := fp_format FMT_D.
(* [comment removed for export] *)
Definition u64 (v : Z) : Z := bv_unsigned (Z_to_bv 64 v).

(* [comment removed for export] *)
Definition EXPF_TAB : list Z :=
  [4607182418800017408; 4607140297302181236; 4607100335213349135; 4607062579818421073;
   4607027079437701499; 4606993883449571754; 4606963042313658936; 4606934607594512097;
   4606908631985796885; 4606885169335019979; 4606864274668794914; 4606846004218661165;
   4606830415447468583; 4606817567076339586; 4606807519112221737; 4606800332876043653;
   4606796071031487437; 4606794797614391156; 4606796578062795143; 4606801479247646227;
   4606809569504174299; 4606820918663955941; 4606835598087680144; 4606853680698631517;
   4606875241016906669; 4606900355194379847; 4606929101050434204; 4606961558108475497;
   4606997807633245319; 4607037932668951391; 4607082018078232794; 4607130150581978432].
Definition EXPF_SHIFT : Z := 4843621399236968448.
Definition EXPF_INVLN2N : Z := 4631694138158056190.
Definition EXPF_C0 : Z := 4520605740625372052.
Definition EXPF_C1 : Z := 4552787166160930035.
Definition EXPF_C2 : Z := 4581900536177775318.
(* [comment removed for export] *)
Definition EXPF_HI : Z := 1118925335.
Definition EXPF_LO : Z := 3268407732.

(* [comment removed for export] *)
Definition expf_main (x : Z) : Z :=
  let cv := fst (fp_convert ES ED RNE x) in
  let z1 := fst (fp_mul ED RNE EXPF_INVLN2N (u64 cv)) in
  let kd := fst (fp_add ED RNE (u64 z1) EXPF_SHIFT) in
  let kd2 := fst (fp_sub ED RNE (u64 kd) EXPF_SHIFT) in
  let rr := fst (fp_sub ED RNE (u64 z1) (u64 kd2)) in
  let t := nth (Z.to_nat (bv_unsigned (v_andi (Z_to_bv 64 kd) 31))) EXPF_TAB 0 in
  let sw := bv_unsigned (v_add (Z_to_bv 64 t) (v_slli (Z_to_bv 64 kd) 47)) in
  let p1 := fst (fp_fma ED RNE EXPF_C0 (u64 rr) EXPF_C1) in
  let r2 := fst (fp_mul ED RNE (u64 rr) (u64 rr)) in
  let one := fst (fp_of_int ED RNE true 32 (u64 1)) in
  let p2 := fst (fp_fma ED RNE EXPF_C2 (u64 rr) (u64 one)) in
  let y := fst (fp_fma ED RNE (u64 p1) (u64 r2) (u64 p2)) in
  let ys := fst (fp_mul ED RNE (u64 y) sw) in
  fst (fp_convert ED ES RNE (u64 ys)).

(* [comment removed for export] *)
Definition EXPF_OFLOW : Z := 2139095040.
Definition EXPF_UFLOW : Z := 0.

Definition expf_model (w : bv 32) : Z :=
  let x := bv_unsigned w in
  let top := v_srli (v_slli (sext 64 w) 33) 53 in
  if c_ltu top (Z_to_bv 64 1067) then expf_main x
  else if c_eq (v_andi (Z_to_bv 64 (fp_class ES x)) 1) (Z_to_bv 64 0) then
         if c_ltu top (Z_to_bv 64 2040) then
           if c_eq (if fst (fp_lt ES EXPF_HI x) then Z_to_bv 64 1 else Z_to_bv 64 0) (Z_to_bv 64 0) then
             if c_eq (if fst (fp_lt ES x EXPF_LO) then Z_to_bv 64 1 else Z_to_bv 64 0) (Z_to_bv 64 0) then expf_main x else EXPF_UFLOW
           else EXPF_OFLOW
         else fst (fp_add ES RNE x x)
       else 0.

(* [comment removed for export] *)
Definition fneg32 (x : Z) : Z := bv_unsigned (sgnj_val F_SGNJN (Z_to_bv 32 x) (Z_to_bv 32 x)).
Definition bil_arg (denom i : Z) : Z :=
  fst (fp_div ES RNE (fneg32 (fst (fp_of_int ES RNE false 32 (u64 (i * i))))) denom).
Definition bil_cell (denom i : Z) : Z := bv_unsigned (Z_to_bv 32 (expf_model (Z_to_bv 32 (bil_arg denom i)))).

(* [comment removed for export] *)
Definition u32 (v : Z) : Z := bv_unsigned (Z_to_bv 32 v).
Definition gauss_arg (den_d q : Z) : Z :=
  fst (fp_convert ED ES RNE (u64 (fst (fp_div ED RNE (u64 (fst (fp_convert ES ED RNE (fneg32 (fst (fp_of_int ES RNE false 32 (u64 q))))))) den_d)))).
Definition gauss_cell (den_d maxv q : Z) : Z := u32 (fst (fp_mul ES RNE maxv (u32 (expf_model (Z_to_bv 32 (gauss_arg den_d q)))))).

(* [comment removed for export] *)
Lemma bil_cell_0 : bil_cell 1112014848 0 = 1065353216.
Proof.
ltac2:(KReplay.run1 (kr_t_ExpfModelB ()) [] "p;1p;2p;3g0000j11Tg000Uj12Tg001:j14Tg001Xj27Tg0022j26Tg0031j35Tf0R0#2#2p=3%20#2#2#2p=0g003KR0g003iR1#1#1#1#1#1#1#2#3#0#0#0#0#0#4R2'7%01#1#3#1#3#1#2#3#0#0#0#0#4g004N'6=502do"). Qed.
Lemma bil_cell_far : bil_cell 1128792064 255 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_ExpfModelB ()) [] "p;2p;1p;3g001Xj27Tg0000j10Tg000Uj11Tg001:j13Tg0022j26Tg0031j35Tf0R0#1#1#1#1p=2%10#1p=4g003KR0g004NR1'7g003iR2#2#0#0#1#0#4#0#1#4#2#2#2#2#3%02#0#0#0#0#0#0#3'6=501do"). Qed.
