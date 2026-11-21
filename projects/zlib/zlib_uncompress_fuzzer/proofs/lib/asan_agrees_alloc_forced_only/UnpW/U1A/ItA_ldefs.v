(* reloc-zl14c *)
(* [U14] inflate_state arrays at their 1.4 offsets (lens 168, work 808, codes 1384, sane 7160; 1.3.1: 152, 792, 1368, 7144) *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW Require Import AImg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState Inftrees ItableModel.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AArr U2AKit ItAKit ItAPure.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.U1A Require Import ItA_base.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_base | solve_load_sh0 | solve_load_image ].
Local Ltac acc_hint ::= acc_hint_sh.

(* [comment removed for export] *)
Definition lowS (z : Z) : Z := if z =? 4294967295 then -1 else z.
(* [U14] 1.4's CODES case stores null base / extra (0x95de4 sd zero,48(s1); 0x95de8 sd zero,40(s1));
   1.3.1 stored the work pointer.  CODES never reads them (every code-length symbol is below match = 20). *)
Definition EXA (ty : codetype) (S : Z) : Z := match ty with CODES => 0 | LENS => 149312 | DISTS => 149504 end.
Definition BSA (ty : codetype) (S : Z) : Z := match ty with CODES => 0 | LENS => 149216 | DISTS => 149408 end.
Definition NE (ty : codetype) : Z := match ty with CODES => 288 | LENS => 31 | DISTS => 32 end.
Definition isL (ty : codetype) : Z := match ty with LENS => 1 | _ => 0 end.
Definition isD (ty : codetype) : Z := match ty with DISTS => 1 | _ => 0 end.

Lemma NE_ext_len : forall ty, NE ty = it_ext_len ty 288.
Proof. destruct ty; reflexivity. Qed.
Lemma ty_cases : forall ty S,
  (ty = CODES /\ cty ty = 0 /\ it_match ty = 20 /\ EXA ty S = 0 /\ BSA ty S = 0 /\ NE ty = 288 /\ isL ty = 0 /\ isD ty = 0)
  \/ (ty = LENS /\ cty ty = 1 /\ it_match ty = 257 /\ EXA ty S = 149312 /\ BSA ty S = 149216 /\ NE ty = 31 /\ isL ty = 1 /\ isD ty = 0)
  \/ (ty = DISTS /\ cty ty = 2 /\ it_match ty = 0 /\ EXA ty S = 149504 /\ BSA ty S = 149408 /\ NE ty = 32 /\ isL ty = 0 /\ isD ty = 1).
Proof. intros ty S. destruct ty; [left | right; left | right; right]; repeat split; reflexivity. Qed.

Lemma pow2_le15 : forall k, 0 <= k <= 15 -> 1 <= 2 ^ k <= 32768.
Proof. intros k Hk. split; [apply (Z.pow_le_mono_r 2 0 k); lia | apply (Z.pow_le_mono_r 2 k 15); lia]. Qed.
Lemma ne_pow : forall ty k, 1 <= k <= 15 ->
  it_not_enough ty (itm_used k) = match ty with CODES => false | _ => negb (k <=? 9) end.
Proof.
  intros ty k Hk. rewrite itm_used_pow2 by lia. unfold it_not_enough, ENOUGH_LENS, ENOUGH_DISTS.
  destruct ty; [reflexivity| |].
  - destruct (Z.leb_spec k 9); cbn [negb].
    + apply Z.ltb_ge. assert (2 ^ k <= 2 ^ 9) by (apply Z.pow_le_mono_r; lia). change (2 ^ 9) with 512 in *. lia.
    + apply Z.ltb_lt. assert (2 ^ 10 <= 2 ^ k) by (apply Z.pow_le_mono_r; lia). change (2 ^ 10) with 1024 in *. lia.
  - destruct (Z.leb_spec k 9); cbn [negb].
    + apply Z.ltb_ge. assert (2 ^ k <= 2 ^ 9) by (apply Z.pow_le_mono_r; lia). change (2 ^ 9) with 512 in *. lia.
    + apply Z.ltb_lt. assert (2 ^ 10 <= 2 ^ k) by (apply Z.pow_le_mono_r; lia). change (2 ^ 10) with 1024 in *. lia.
Qed.

(* [comment removed for export] *)
Lemma mxmn_facts_g : forall lf lo codes bits, 1 <= mxA lf lo codes ->
  1 <= mnA lf lo codes <= mxA lf lo codes /\ mxA lf lo codes <= 15 /\ 1 <= rootA lf lo codes bits <= 15 /\
  mnA lf lo codes <= rootA lf lo codes bits /\
  rootA lf lo codes bits = (let r := (if bits <? mxA lf lo codes then bits else mxA lf lo codes) in
                            if mnA lf lo codes <? r then r else mnA lf lo codes).
Proof.
  intros lf lo codes bits H1. pose proof (mx_range (cntA lf lo codes)) as MR.
  pose proof (mn_range (cntA lf lo codes) (mxA lf lo codes) ltac:(unfold mxA in *; lia)) as NR.
  unfold rootA, itm_root. unfold mnA in *. unfold mxA in *.
  set (mxv := itm_max (cntA lf lo codes)) in *. set (mnv := itm_min (cntA lf lo codes) mxv) in *.
  destruct (Z.ltb_spec mxv bits); destruct (Z.ltb_spec bits mxv); try lia;
    destruct (Z.ltb_spec mxv mnv); destruct (Z.ltb_spec bits mnv); destruct (Z.ltb_spec mnv mxv); destruct (Z.ltb_spec mnv bits); cbv zeta; lia.
Qed.
Lemma rt_facts : forall lf lo codes bits, 1 <= mxA lf lo codes ->
  1 <= rootA lf lo codes bits <= 15 /\ mnA lf lo codes <= rootA lf lo codes bits <= mxA lf lo codes /\ 1 <= mnA lf lo codes.
Proof.
  intros lf lo codes bits H. pose proof (mxmn_facts_g lf lo codes bits H) as (A & B & D & E & F). cbv zeta in F.
  destruct (Z.ltb_spec bits (mxA lf lo codes)); [destruct (Z.ltb_spec (mnA lf lo codes) bits) | destruct (Z.ltb_spec (mnA lf lo codes) (mxA lf lo codes))]; lia.
Qed.

(* [comment removed for export] *)
Lemma sllw_1 : forall k, 0 <= k <= 15 -> bv_swrap 32 (Z.shiftl 1 (k mod 32)) = 2 ^ k.
Proof.
  intros k Hk. rewrite Z.mod_small by lia. rewrite Z.shiftl_1_l. pose proof (pow2_le15 k Hk). apply swrap32_small. lia.
Qed.
Lemma sllw_m1 : forall k, 0 <= k <= 15 -> bv_swrap 32 (Z.shiftl (-1) (k mod 32)) = - 2 ^ k.
Proof.
  intros k Hk. rewrite Z.mod_small by lia. rewrite Z.shiftl_mul_pow2 by lia. pose proof (pow2_le15 k Hk).
  rewrite swrap32_small by lia. lia.
Qed.
Lemma srlw_small : forall a b, 0 <= a < 2147483648 -> 0 <= b < 32 ->
  bv_swrap 32 (Z.shiftr (a mod 4294967296) (b mod 32)) = Z.shiftr a b.
Proof.
  intros a b Ha Hb. rewrite !Z.mod_small by lia.
  assert (0 <= Z.shiftr a b <= a).
  { rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 b ltac:(lia) ltac:(lia)).
    split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; [lia | nia]]. }
  apply swrap32_small. lia.
Qed.
Lemma wrap8_mod : forall z, wrap8 z = z mod 256.
Proof. intros z. unfold wrap8. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma lowS_small : forall z, 0 <= z < 4294967295 -> lowS z = z.
Proof. intros z Hz. unfold lowS. destruct (Z.eqb_spec z 4294967295); [lia | reflexivity]. Qed.
Lemma sextw_lowS : forall z, (z = 4294967295 \/ 0 <= z < 32768) ->
  Z_to_bv 64 (bv_swrap 32 (lowS z mod 18446744073709551616 + 0)) = Z_to_bv 64 (lowS z).
Proof.
  intros z [->|Hz]; [reflexivity|]. rewrite lowS_small by lia. rewrite Z.mod_small by lia. rewrite Z.add_0_r.
  rewrite swrap32_small by lia. reflexivity.
Qed.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition mst (SP SPA S F PB LP : Z) (gp tp : word) (FR : bvmap 5 word) (fc : bv 32) (rt mx : Z) (st : ItSt)
    (x1 y1 y2 x10 x11 x16 y7 x25 x28 x29 : word) (pc : Z) (m : amem) : machine_state :=
  (* [U14] 1.4's table loop keeps drop in a7 (1.3.1: t0), and its temporaries t1 / t2 / a7 of 1.3.1 are
     t2 / t1 / t0 at 1.4 (tools/align_blocks_gr.py over inflate_table: 871 of 905 instructions aligned; a7 <-> t0 47 votes,
     t1 <-> t2 31); the binders keep their 1.3.1 order, so every caller's argument keeps its meaning *)
  bst SP SPA S F PB LP gp tp FR fc x1 y7 y2 y1 x10 x11 (Z_to_bv 64 (Z.shiftr PB 3 + 2147450880))
      (Z_to_bv 64 rt) (Z_to_bv 64 mx) (Z_to_bv 64 (t_len st)) x16 (Z_to_bv 64 (t_drop st)) (Z_to_bv 64 (t_huff st)) x25 x28 x29
      (Z_to_bv 64 (S + 1384 + 4 * t_next st)) (Z_to_bv 64 (t_sym st)) pc m.

(* [comment removed for export] *)
Definition minv (SPA S F PB : Z) (m1 m : amem) (ty : codetype) (rt nx bits : Z) (lf w1 : Z -> Z) (st : ItSt)
    (v0 v96 v104 v112 : word) (of : Z -> Z) : Prop :=
  itb_inv SPA S F PB m1 m v0 (Z_to_bv 64 (isD ty)) (Z_to_bv 64 (isL ty)) (Z_to_bv 64 (Z.shiftr (S + 160) 3 + 2147450880))
          (* [U14] 1.4 keeps extra in frame slot 40 and base in 48 (1.3.1: base 40, extra 48); here's
             0x95f1c ld a6,40(s1) reads op, 0x95f3c ld a6,48(s1) reads val *)
          (Z_to_bv 64 (t_used st)) (Z_to_bv 64 (EXA ty S)) (Z_to_bv 64 (BSA ty S)) (Z_to_bv 64 (2 ^ rt - 1))
          (Z_to_bv 64 (lowS (t_low st))) (Z_to_bv 64 (it_match ty)) (Z_to_bv 64 (2 ^ t_curr st)) (Z_to_bv 64 (S + 160))
          v96 v104 v112 (arr_get (t_count st)) of lf w1 (arr_get (t_tbl st))
          (Z_to_bv 64 (S + 1384 + 4 * nx)) (Z_to_bv 64 bits).

(* [comment removed for export] *)
Definition ret_pre (SP SPA S F PB LP : Z) (gp tp : word) (FR : bvmap 5 word) (fc : bv 32) (m1 : amem)
    (r : Z) (lf wf' cf' : Z -> Z) (next' bits' : word) : machine_state -> Prop :=
  fun ms' => exists (m : amem) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 : word)
                    (v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 : word) (cnt of : Z -> Z),
    ms' = bst SP SPA S F PB LP gp tp FR fc x1 x5 x6 x7 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 0x96348 m
    /\ itb_inv SPA S F PB m1 m v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 cnt of lf wf' cf' next' bits'.

End CANSEC1.

(* [comment removed for export] *)
Definition spure (work1 : arr) (rt nx : Z) (st : ItSt) : Prop :=
  t_work st = work1 /\ BOX (t_low st = 4294967295 \/ 0 <= t_low st < 32768) /\ BOX (t_drop st = 0 \/ t_drop st = rt) /\
  0 <= t_next st /\ nx <= t_next st /\
  (forall j, 0 <= j < 16 -> 0 <= arr_get (t_count st) j < 65536) /\
  (forall j, 0 <= j < 1444 -> 0 <= arr_get (t_tbl st) j < 4294967296) /\
  arr_len (t_count st) = 16 /\ arr_len (t_tbl st) = 1444.
Ltac open_spure H :=
  let H' := fresh "SPc" in pose proof H as H';
  destruct H' as (WK & LOWR & DROPR & NX0 & NX1 & HCr & HTr & CL & TL).
