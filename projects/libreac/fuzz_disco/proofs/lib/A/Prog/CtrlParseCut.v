(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: relocated from the walk of the same function of libreac's fuzz_grant (the two are the same code at other addresses); the context, the cut specifications and the tactics are restated on fuzz_disco's contract, treac_ctrl_parse_spec. *)
(* reac_ctrl_parse (0x6464) of fuzz_disco's ASan build: the cuts its walk is split at, over the contract
   of lib/A/Prog/CtrlParse.v (the caller-journal form: it writes the caller's `struct reac_ctrl_parsed`).
   CtrlParseWalk.v goes from the entry to cut A (the side-stack frame taken); CtrlParseMid.v from cut A to
   cut M; CtrlParseNone.v and CtrlParseAcc.v from cut M to cut J / cut B; CtrlParseTail.v from cut B to
   cut J; CtrlParseEpi.v from cut J (every path's join) to the return. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0s YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaRun PaShadow PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoBase YC81 YC4b YC1g YC1h YC45 YC85 DiscoFrame YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import RcKind RcParse.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import CtrlParse CtrlParseLib KindOfLink1 DiscoRo ACj1 DiscoACja.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
#[local] Ltac Zify.zify_pre_hook ::= try unfold YImgTop.IMG_TOP, YImgTop.IMG_LO in *.
(* Cut A, at AF_CUTA = AF_reac_ctrl_parse + 0x74 (after __asan_stack_malloc_1 returns, the frame (1, fpos)
   seated): the state the walk reaches; CtrlParseMid.v starts here. *)
Definition ss_cutA : sstate := Eval vm_compute in
(mkSS AF_CUTA
   [SLit 0; SOff 512 0; SOff 33 0; SOff 3 0; SOff 4 0; 
    SOff 513 0; SOff 514 0; SOff 515 0; SOff 2 0; 
    SOff 33 0; SOff 516 0; SOff 517 0; SOff 518 0; 
    SOff 519 0; SOff 520 0; SOff 521 0; SOff 522 0; 
    SOff 523 0; SOff 18 0; SOff 19 0; SOff 12 0; SOff 10 0; 
    SOff 11 0; SOff 23 0; SOff 24 0; SOff 32 0; SOff 26 0; 
    SOff 27 0; SOff 524 0; SOff 525 0; SOff 526 0; 
    SOff 527 0]
   [{|
      r_base := Some 529%nat;
      r_lo := 0;
      r_hi := 16;
      r_wlo := 0;
      r_whi := 16;
      r_chunks :=
        [{| c_off := 0; YP09.c_val := CVal 8 (SLit 0) |};
         {| c_off := 8; YP09.c_val := CVal 8 (SLit 0) |}]
    |};
    {|
      r_base := Some 516%nat;
      r_lo := 0;
      r_hi := 128;
      r_wlo := 0;
      r_whi := 128;
      r_chunks := [{| c_off := 120; YP09.c_val := CVal 8 (SOff 528 0) |}]
    |};
    {|
      r_base := Some 33%nat;
      r_lo := 0;
      r_hi := 32;
      r_wlo := 0;
      r_whi := 32;
      r_chunks := []
    |};
    {|
      r_base := Some 2%nat;
      r_lo := -96;
      r_hi := 0;
      r_wlo := -96;
      r_whi := 0;
      r_chunks :=
        [{| c_off := -96; YP09.c_val := CVal 8 (SOff 26 0) |};
         {| c_off := -88; YP09.c_val := CVal 8 (SOff 25 0) |};
         {| c_off := -80; YP09.c_val := CVal 8 (SOff 24 0) |};
         {| c_off := -72; YP09.c_val := CVal 8 (SOff 23 0) |};
         {| c_off := -64; YP09.c_val := CVal 8 (SOff 22 0) |};
         {| c_off := -56; YP09.c_val := CVal 8 (SOff 21 0) |};
         {| c_off := -48; YP09.c_val := CVal 8 (SOff 20 0) |};
         {| c_off := -40; YP09.c_val := CVal 8 (SOff 19 0) |};
         {| c_off := -32; YP09.c_val := CVal 8 (SOff 18 0) |};
         {| c_off := -24; YP09.c_val := CVal 8 (SOff 9 0) |};
         {| c_off := -16; YP09.c_val := CVal 8 (SOff 8 0) |};
         {| c_off := -8; YP09.c_val := CVal 8 (SOff 1 0) |}]
    |};
    {|
      r_base := Some 241%nat;
      r_lo := 0;
      r_hi := 8;
      r_wlo := 0;
      r_whi := 0;
      r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 308 0) |}]
    |};
    {|
      r_base := Some 308%nat;
      r_lo := 0;
      r_hi := 4;
      r_wlo := 0;
      r_whi := 0;
      r_chunks := [{| c_off := 0; YP09.c_val := CVal 4 (SLit 1) |}]
    |};
    {|
      r_base := Some 242%nat;
      r_lo := 0;
      r_hi := 8;
      r_wlo := 0;
      r_whi := 0;
      r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 307 0) |}]
    |};
    {|
      r_base := Some 307%nat;
      r_lo := 0;
      r_hi := 8;
      r_wlo := 0;
      r_whi := 0;
      r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 32 0) |}]
    |};
    {|
      r_base := Some 10%nat;
      r_lo := 0;
      r_hi := 50;
      r_wlo := 0;
      r_whi := 0;
      r_chunks :=
        [{| c_off := 0; YP09.c_val := CVal 1 (SOff 40 0) |};
         {| c_off := 1; YP09.c_val := CVal 1 (SOff 41 0) |};
         {| c_off := 2; YP09.c_val := CVal 1 (SOff 42 0) |};
         {| c_off := 3; YP09.c_val := CVal 1 (SOff 43 0) |};
         {| c_off := 4; YP09.c_val := CVal 1 (SOff 44 0) |};
         {| c_off := 5; YP09.c_val := CVal 1 (SOff 45 0) |};
         {| c_off := 6; YP09.c_val := CVal 1 (SOff 46 0) |};
         {| c_off := 7; YP09.c_val := CVal 1 (SOff 47 0) |};
         {| c_off := 8; YP09.c_val := CVal 1 (SOff 48 0) |};
         {| c_off := 9; YP09.c_val := CVal 1 (SOff 49 0) |};
         {| c_off := 10; YP09.c_val := CVal 1 (SOff 50 0) |};
         {| c_off := 11; YP09.c_val := CVal 1 (SOff 51 0) |};
         {| c_off := 12; YP09.c_val := CVal 1 (SOff 52 0) |};
         {| c_off := 13; YP09.c_val := CVal 1 (SOff 53 0) |};
         {| c_off := 14; YP09.c_val := CVal 1 (SOff 54 0) |};
         {| c_off := 15; YP09.c_val := CVal 1 (SOff 55 0) |};
         {| c_off := 16; YP09.c_val := CVal 1 (SOff 56 0) |};
         {| c_off := 17; YP09.c_val := CVal 1 (SOff 57 0) |};
         {| c_off := 18; YP09.c_val := CVal 1 (SOff 58 0) |};
         {| c_off := 19; YP09.c_val := CVal 1 (SOff 59 0) |};
         {| c_off := 20; YP09.c_val := CVal 1 (SOff 60 0) |};
         {| c_off := 21; YP09.c_val := CVal 1 (SOff 61 0) |};
         {| c_off := 22; YP09.c_val := CVal 1 (SOff 62 0) |};
         {| c_off := 32; YP09.c_val := CVal 1 (SOff 72 0) |};
         {| c_off := 33; YP09.c_val := CVal 1 (SOff 73 0) |};
         {| c_off := 34; YP09.c_val := CVal 1 (SOff 74 0) |};
         {| c_off := 35; YP09.c_val := CVal 1 (SOff 75 0) |};
         {| c_off := 36; YP09.c_val := CVal 1 (SOff 76 0) |};
         {| c_off := 37; YP09.c_val := CVal 1 (SOff 77 0) |};
         {| c_off := 38; YP09.c_val := CVal 1 (SOff 78 0) |}]
    |};
    {|
      r_base := Some 12%nat;
      r_lo := 0;
      r_hi := 36;
      r_wlo := 0;
      r_whi := 36;
      r_chunks := []
    |}]
   None
   {|
     f_atoms :=
       [(529%nat,
         {| af_lo := 2147451392; af_hi := 17594333495296; af_al2 := 2 |});
        (528%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 0 |});
        (516%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 5 |});
        (33%nat,
         {| af_lo := 70368744177152; af_hi := 140737488355328; af_al2 := 5 |});
        (2%nat,
         {| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 4 |});
        (10%nat, {| af_lo := 1; af_hi := 2 ^ 47 - 50; af_al2 := 0 |});
        (11%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |});
        (12%nat, {| af_lo := 4096; af_hi := 2 ^ 47 - 36; af_al2 := 3 |});
        (32%nat, {| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |});
        (40%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
        (41%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
        (42%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
        (43%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
        (44%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
        (45%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
        (46%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
        (47%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
        (48%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
        (49%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
        (50%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
        (51%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
        (52%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
        (53%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
        (54%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
        (55%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
        (56%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
        (57%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
        (58%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
        (59%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
        (60%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
        (61%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
        (62%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
        (63%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
        (64%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
        (65%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
        (66%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
        (67%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
        (68%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
        (69%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
        (70%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
        (71%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
        (72%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
        (73%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
        (74%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
        (75%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
        (76%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
        (77%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
        (78%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |})];
     f_conds := [];
     f_alias :=
       [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 32 0),
         SOff 529 0)]
   |}).
Ltac pz_win_tac Hrw :=
let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
let Hin := fresh "Hin" in let Ha := fresh "Ha" in let Hq := fresh "Hq" in
intros b wlo whi a Hin Ha;
lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In (b, wlo, whi) l') in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Ha; Hrw Ha; cbv beta; first [lia | match goal with H : ?t |- ?g => idtac "WINFAIL" t g end; fail] |]); destruct Hin.
(* Rebase the walk's valuation after a havoc above the image atoms: the facts about the old atoms carry over. *)
Ltac pz_rebase HS AGX :=
lazymatch type of HS with st_ok_pi _ _ (havoc ?Eo ?kk ?ws) _ _ =>
first [ let _H := rnHEI constr:(havoc Eo kk ws) in idtac
| lazymatch goal with Ho : img_env _ _ Eo |- _ => let H := fresh "HEI" in pose proof (img_env_havoc_hi Eo kk ws Ho ltac:(cbv; lia)) as H end ];
let Ev := fresh "E" in let HEv := fresh "HEv" in
remember (havoc Eo kk ws) as Ev eqn:HEv in *;
let AGX2 := fresh "AGX" in
lazymatch type of AGX with forall n, (n < ?K)%nat -> ew Eo n = ew ?E0 n =>
assert (AGX2 : forall n, (n < K)%nat -> ew Ev n = ew E0 n)
by (let nn := fresh "nn" in let Hnn := fresh "Hnn" in intros nn Hnn; rewrite HEv, ew_havoc_old by lia; apply AGX; exact Hnn) end;
clear AGX; rename AGX2 into AGX;
repeat match goal with H : ew Eo ?n = ?v |- _ =>
let H2 := fresh in assert (H2 : ew Ev n = v) by (rewrite HEv, ew_havoc_old by (cbv; lia); exact H); clear H; rename H2 into H end;
repeat match goal with H : img_env _ _ Eo |- _ => clear H end;
clear HEv end.
(* The values of the region bases in a goal. *)
Ltac pz_bases :=
try lazymatch goal with AGX : forall n, (n < 512)%nat -> ew _ n = ew _ n |- _ =>
rewrite ?(AGX 2%nat), ?(AGX 10%nat), ?(AGX 12%nat), ?(AGX 33%nat), ?(AGX 241%nat), ?(AGX 242%nat), ?(AGX 307%nat), ?(AGX 308%nat) by lia end;
lazymatch goal with
| Usp : bv_unsigned (ew ?E0 2) = _, B10 : bv_unsigned (ew ?E0 10) = _, B12 : bv_unsigned (ew ?E0 12) = _, B33 : bv_unsigned (ew ?E0 33) = _,
  B241 : bv_unsigned (ew ?E0 241) = _, B242 : bv_unsigned (ew ?E0 242) = _, B307 : bv_unsigned (ew ?E0 307) = _, B308 : bv_unsigned (ew ?E0 308) = _ |- _ =>
rewrite ?Usp, ?B10, ?B12, ?B33, ?B241, ?B242, ?B307, ?B308 end;
repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
rewrite ?unsigned_lit_small by (unfold SB; lia).
(* The walk's own write windows: the machine stack below the entry sp, the realigned stack and the out struct. *)
Ltac pz_awr_hd :=
lazymatch goal with
| |- awr_ok _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _ :: _) _ ?s0 _ _ _ _ _ =>
lazymatch goal with Usp : bv_unsigned (ew _ 2) = ?spv |- _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spv - s0)); [reflexivity | pz_bases; lia | cbn; lia | cbn; lia |] end
| |- awr_ok _ (YP09.mkRegion (Some 33%nat) _ _ _ _ _ :: _) _ ?s0 _ _ _ _ _ =>
lazymatch goal with B33 : bv_unsigned (ew _ 33) = ?spv |- _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 33%nat (spv - s0)); [reflexivity | pz_bases; lia | cbn; lia | cbn; lia |] end
| |- awr_ok _ (YP09.mkRegion (Some 12%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
lazymatch goal with B12 : bv_unsigned (ew _ 12) = ?ov, HOW : forall a, _ -> awr_byte _ _ _ _ _ _ _ a /\ _, Eab : ablocks _ _ ?S2 = ablocks _ _ _ |- _ =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 12%nat ov); [reflexivity | pz_bases; lia | | ];
[ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; rewrite ?Eab; apply pz_awr_cons; exact (proj1 (HOW a ltac:(lia))) | ] end
end.
Ltac pz_norm HS := lazymatch type of HS with st_ok_pi _ _ _ ?ss _ => let v := eval vm_compute in ss in change ss with v in HS end.
Section b. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
(* The image addresses this walk uses, each named once (fuzz_disco relocates them). *)
Definition OBJ_BCAST : nat := 58%nat.
(* The machine stack the call needs is REAC_CTRL_PARSE_STK (lib/A/Prog/CtrlParse.v): its own 128-byte
   frame, realigned down to 32 bytes (at most 16 more), and below that 2 * ESTACK, which the bcmp
   wrapper's contract (abcmp_realizes) asks for; the other runtime entries and kind_of_link1
   (KIND_OF_LINK1_STK = ESTACK) need less. *)
Definition PZspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* The stack region below the 128-byte frame, after the realignment of sp: it keeps the saved registers. *)
Definition pz_trim (rs : smem) : smem :=
map (fun r => match YP09.r_base r with
| Some 2%nat => YP09.mkRegion (Some 2%nat) (-96) 0 (-96) 0 (List.filter (fun c => -96 <=? YP09.c_off c) (YP09.r_chunks r))
| _ => r end) rs.
(* The static context of the walk once the frame is taken: the contract's premises and the frame
   (1, fpos) of the post-allocation state S2. fuzz_grant's context named a caller frame for each of f
   and o; fuzz_disco's contract names none, so the two are placed by pz_loc / awr_byte instead. *)
Record pz_ctx : Type := mkPZ {
cx_fq : YK11.FPState;
cx_STK : Z; cx_sp0 : Z; cx_FP : list (Z * Z); cx_ly : alayout; cx_S : astate; cx_W0 : world SEGS;
cx_mem0 : word -> option byte; cx_md0 : Model; cx_own : list (Z * Z); cx_lyc : alayout; cx_Sc : astate;
cx_W : world SEGS; cx_memc : word -> option byte; cx_mdc : Model; cx_k : Z; cx_regs : bvmap 5 word;
cx_ch : list (Z * Z * Z); cx_f : Z; cx_n : Z; cx_o : Z; cx_fr : list byte; cx_S2 : astate; cx_fpos : Z }.
(* The runtime entries and the image facts the walk takes, one Prop. The entries that read or write the
   machine state are quantified over the floating-point state, as fuzz_disco's walks state them. *)
Definition pz_rt (B : asyms) (G : list (Z * Z)) : Prop :=
AR_laws SEGS B /\ PALib B /\ PALibF B /\ model_laws (as_universe B) /\
(forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OSet (SIGMA DS___asan_memset)) /\
(forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OCpy (SIGMA DS___asan_memcpy)) /\
(forall fq : YK11.FPState, abcmp_realizes (fx := fq) SEGS B (SIGMA DS___interceptor_trampoline_bcmp)) /\
(forall fq : YK11.FPState, astack_malloc_realizes (fx := fq) SEGS B 1) /\
stack_malloc_progressP B /\ astack_free_law SEGS B /\ frame_flag_lawP SEGS B /\ tkind_of_link1_spec B /\
globs_marked SEGS B G /\ In (VAL (A_OBJ OBJ_BCAST), 7) G /\ img_shadow_vis SEGS B /\
(IMG_LO + 64 <= VAL (A_OBJ OBJ_BCAST) /\ VAL (A_OBJ OBJ_BCAST) + 6 + 64 <= IMG_TOP) /\
(forall (H : word -> bool) mem, arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
forall i, 0 <= i < 6 -> aview SEGS H mem (VAL (A_OBJ OBJ_BCAST) + i) = Some 255).
(* The contract's premises, plus the frame (1, fpos) the call took. The premises about f hold under
   50 <= n only, as treac_ctrl_parse_spec states them. *)
Definition pz_ok (B : asyms) (c : pz_ctx) : Prop :=
ajournal SEGS B (cx_STK c) (cx_sp0 c) (cx_FP c) (cx_ly c) (cx_S c) (cx_W0 c) (cx_mem0 c) (cx_md0 c) (cx_own c) (cx_lyc c) (cx_Sc c) (cx_W c) (cx_memc c) (cx_mdc c) (cx_k c) /\
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H (cx_W c)) (cx_memc c)) /\
YK0s.ret_ok (getr (cx_regs c) 1) /\ 4096 <= raZ (cx_regs c) /\
getr (cx_regs c) 3 = w64 (as_gp B) /\ getr (cx_regs c) 4 = w64 (as_tp B) /\
getr (cx_regs c) 10 = w64 (cx_f c) /\ getr (cx_regs c) 11 = w64 (cx_n c) /\ getr (cx_regs c) 12 = w64 (cx_o c) /\ 0 <= (cx_n c) < 2 ^ 64 /\
achain (cx_lyc c) (aview SEGS (w_H (cx_W c)) (cx_memc c)) (spZ (cx_regs c)) (s0Z (cx_regs c)) (cx_ch c) /\
spZ (cx_regs c) mod 16 = 0 /\ (cx_sp0 c) - (cx_STK c) <= spZ (cx_regs c) - REAC_CTRL_PARSE_STK /\ spZ (cx_regs c) <= (cx_sp0 c) /\
spZ (cx_regs c) + 32 <= ly_top (cx_lyc c) /\
Z.of_nat (length (frames (cx_Sc c))) <= REAC_CTRL_PARSE_DEPTH /\
length (cx_fr c) = 50%nat /\
(50 <= (cx_n c) -> pz_fok B (cx_lyc c) (cx_Sc c) (cx_W c) (cx_memc c) (spZ (cx_regs c)) (cx_f c) (cx_o c) (cx_fr c)) /\
pz_ook B (cx_STK c) (cx_sp0 c) (cx_FP c) (cx_ly c) (cx_S c) (cx_lyc c) (cx_Sc c) (cx_own c) (cx_W c) (cx_memc c) (spZ (cx_regs c)) (cx_o c) /\
frames (cx_S2 c) = (1, (cx_fpos c)) :: frames (cx_Sc c) /\ ablocks B (cx_lyc c) (cx_S2 c) = ablocks B (cx_lyc c) (cx_Sc c) /\ ~ In (1, (cx_fpos c)) (frames (cx_Sc c)) /\
(exists ff, (cx_S2 c) = set_fs ff (cx_Sc c)).
(* The entry valuation (pz_extra: atom 32 SB, 33 the realigned sp, 40 + i the frame byte i). *)
Definition pz_E0 (c : pz_ctx) : env := Eimg (Ereg (cx_regs c) (pz_extra (spZ (cx_regs c)) (cx_fr c))).
(* What holds of the valuation, the journal and the caller's memory at every cut. *)
Definition pz_cur (B : asyms) (c : pz_ctx) (E : env) (ms : machine_state) (md : Model) : Prop :=
img_env VAL A_LIM E /\
(forall n0, (n0 < 512)%nat -> ew E n0 = ew (pz_E0 c) n0) /\
ew E 516 = Z_to_bv 64 (frame_addr (cx_lyc c) 1 (cx_fpos c)) /\ ew E 528 = Z_to_bv 64 (flag_addr (cx_lyc c) 1 (cx_fpos c)) /\
ew E 529 = Z_to_bv 64 (SB + frame_addr (cx_lyc c) 1 (cx_fpos c) / 8) /\
ajournal SEGS B (cx_STK c) (cx_sp0 c) (cx_FP c) (cx_ly c) (cx_S c) (cx_W0 c) (cx_mem0 c) (cx_md0 c) ((1, (cx_fpos c)) :: (cx_own c)) (cx_lyc c) (cx_S2 c) (cx_W c) (ms_mem ms) md (cx_k c) /\
pz_kept B (cx_lyc c) (cx_Sc c) (cx_W c) (cx_memc c) (ms_mem ms) (spZ (cx_regs c) - REAC_CTRL_PARSE_STK) (spZ (cx_regs c)) (cx_o c).
Definition pz_post (B : asyms) (c : pz_ctx) : world SEGS -> config -> Prop :=
treac_ctrl_parse_post B (cx_fq c) (cx_STK c) (cx_sp0 c) (cx_FP c) (cx_ly c) (cx_S c) (cx_W0 c) (cx_mem0 c) (cx_md0 c) (cx_own c) (cx_lyc c) (cx_Sc c) (cx_W c) (cx_memc c) (cx_k c) (cx_regs c) (cx_o c) (cx_n c) (cx_fr c).
(* Cut J: a0 (atom 700) is the return code and the out struct holds the model's 36 bytes. Both the walk
   of 50 <= n and the short walk of n < 50 end here. *)
Definition pz_cutJ_spec (B : asyms) (c : pz_ctx) : Prop :=
forall E ms md, pz_cur B c E ms md ->
st_ok_pi (fx := cx_fq c) SEGS VAL E ss_cutJ (restrict (w_H (cx_W c)) ms) ->
ew E 700 = Z_to_bv 64 (fst (ctrlparse (cx_n c) (cx_fr c))) ->
(forall i, (i < 36)%nat -> aview SEGS (w_H (cx_W c)) (ms_mem ms) (cx_o c + Z.of_nat i) =
Some (bv_unsigned (nth i (snd (ctrlparse (cx_n c) (cx_fr c))) cp_z))) ->
SRr SEGS (cx_W c) (mkCfg ms md) (pz_post B c).
(* Cut B: the header was accepted; atom 640 is the bcmp wrapper's result. *)
Definition pz_cutB_spec (B : asyms) (c : pz_ctx) : Prop :=
50 <= cx_n c ->
forall E ms md, pz_cur B c E ms md ->
st_ok_pi (fx := cx_fq c) SEGS VAL E ss_cutB (restrict (w_H (cx_W c)) ms) ->
sh_ok SEGS PZx PZ_SH E (mrestrict (w_H (cx_W c)) (ms_mem ms)) ->
cp_hdr (cx_n c) (cx_fr c) = true ->
(ew E 640 = Z_to_bv 64 0 <-> cp_bcast (cx_fr c) = true) ->
SRr SEGS (cx_W c) (mkCfg ms md) (pz_post B c).
(* Cut M: the memset of the out struct returned and the frame f's region is in the state, which the
   contract gives only under 50 <= n; CtrlParseNone.v takes the paths the header check rejects,
   CtrlParseAcc.v the accepting path. *)
Definition pz_cutM_case (B : asyms) (c : pz_ctx) (P : Prop) : Prop :=
50 <= cx_n c ->
forall E ms md, pz_cur B c E ms md ->
st_ok_pi (fx := cx_fq c) SEGS VAL E ss_cutM (restrict (w_H (cx_W c)) ms) ->
sh_ok SEGS PZx PZ_SH E (mrestrict (w_H (cx_W c)) (ms_mem ms)) ->
P ->
SRr SEGS (cx_W c) (mkCfg ms md) (pz_post B c).
(* Cut B restricted to the frames of one class of frame type and link (CtrlParseTail1..5.v). *)
Definition pz_cutB_case (B : asyms) (c : pz_ctx) (P : list byte -> Prop) : Prop :=
50 <= cx_n c ->
forall E ms md, pz_cur B c E ms md ->
st_ok_pi (fx := cx_fq c) SEGS VAL E ss_cutB (restrict (w_H (cx_W c)) ms) ->
sh_ok SEGS PZx PZ_SH E (mrestrict (w_H (cx_W c)) (ms_mem ms)) ->
cp_hdr (cx_n c) (cx_fr c) = true ->
(ew E 640 = Z_to_bv 64 0 <-> cp_bcast (cx_fr c) = true) ->
P (cx_fr c) ->
SRr SEGS (cx_W c) (mkCfg ms md) (pz_post B c).
(* Cut A: the frame (1, fpos) is seated. *)
Definition pz_cutA_spec (B : asyms) (c : pz_ctx) : Prop :=
50 <= cx_n c ->
forall E ms md, pz_cur B c E ms md ->
st_ok_pi (fx := cx_fq c) SEGS VAL E ss_cutA (restrict (w_H (cx_W c)) ms) ->
SRr SEGS (cx_W c) (mkCfg ms md) (pz_post B c).
(* The five classes of frames at cut B, as Pau's cp_kind (lib/Prog/RcParse.v:22) splits them:
   1 FILLER / MASTER_ANNOUNCE / SPLIT_ANNOUNCE; 2 another frame type (13); 3 link 1 (kind_of_link1);
   4 link 4, the record container (11 / 6 / 5); 5 any other link (12 for link 2, else 13). *)
Definition pz_P1 (fr : list byte) : Prop := cp_type fr 0 0 = true \/ cp_type fr 0xcf 0xea = true \/ cp_type fr 0xce 0xea = true.
Definition pz_P2 (fr : list byte) : Prop :=
cp_type fr 0 0 = false /\ cp_type fr 0xcf 0xea = false /\ cp_type fr 0xce 0xea = false /\ cp_type fr 0xcd 0xea = false.
Definition pz_P3 (fr : list byte) : Prop := cp_type fr 0xcd 0xea = true /\ cp_v fr 18 = 1.
Definition pz_P4 (fr : list byte) : Prop := cp_type fr 0xcd 0xea = true /\ cp_v fr 18 = 4.
Definition pz_P5 (fr : list byte) : Prop := cp_type fr 0xcd 0xea = true /\ cp_v fr 18 <> 1 /\ cp_v fr 18 <> 4.
Lemma pz_cases : forall fr, pz_P1 fr \/ pz_P2 fr \/ pz_P3 fr \/ pz_P4 fr \/ pz_P5 fr.
Proof.
intros fr. unfold pz_P1, pz_P2, pz_P3, pz_P4, pz_P5.
destruct (cp_type fr 0 0); [left; left; reflexivity|].
destruct (cp_type fr 0xcf 0xea); [left; right; left; reflexivity|].
destruct (cp_type fr 0xce 0xea); [left; right; right; reflexivity|].
destruct (cp_type fr 0xcd 0xea); [|right; left; repeat split; reflexivity].
destruct (Z.eq_dec (cp_v fr 18) 1); [right; right; left; split; [reflexivity | assumption]|].
destruct (Z.eq_dec (cp_v fr 18) 4); [right; right; right; left; split; [reflexivity | assumption]|].
right; right; right; right. repeat split; assumption.
Qed.
(* Class 4 split by its paths, for a second attack on CtrlParseTail4.v: the record fragment (11), the head-amp
   record (6), the other records (5). *)
Definition pz_P4a (fr : list byte) : Prop := pz_P4 fr /\ cp_v fr 19 <> 3.
Definition pz_P4b (fr : list byte) : Prop := pz_P4 fr /\ cp_v fr 19 = 3 /\ cp_amp fr = true.
Definition pz_P4c (fr : list byte) : Prop := pz_P4 fr /\ cp_v fr 19 = 3 /\ cp_amp fr = false.
Lemma pz_cases4 : forall fr, pz_P4 fr -> pz_P4a fr \/ pz_P4b fr \/ pz_P4c fr.
Proof.
intros fr H. unfold pz_P4a, pz_P4b, pz_P4c.
destruct (Z.eq_dec (cp_v fr 19) 3) as [E|E]; [|left; exact (conj H E)].
destruct (cp_amp fr) eqn:A; [right; left | right; right]; exact (conj H (conj E eq_refl)).
Qed.
End d.
End b.
(* Open a cut: the context's variables and premises under their standard names. *)
Ltac pz_open c Hok :=
destruct c as [fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch f n o fr S2 fpos];
unfold pz_ok, pz_cur, pz_post, pz_E0, pz_cutJ_spec, pz_cutB_spec, pz_cutM_case, pz_cutB_case, pz_cutA_spec in *;
cbn [pz_ok pz_cur pz_post pz_E0 cx_fq cx_STK cx_sp0 cx_FP cx_ly cx_S cx_W0 cx_mem0 cx_md0 cx_own cx_lyc cx_Sc cx_W cx_memc
cx_mdc cx_k cx_regs cx_ch cx_f cx_n cx_o cx_fr cx_S2 cx_fpos] in *;
destruct Hok as (HJ & HROD & Hra & Hra4 & Hgp & Htp & H10 & H11 & H12 & Hn & Hch & Hal16 & Hwin & Hsp0 & Htop32 &
Hroom & Hflen & HFOK & HOOK & Hfrs2 & Eab & Hnin & ES2);
destruct HOOK as (Ho32 & Ho4096 & Ho47 & Hoam & Hoimg & Hosh & Howin & HRo & HHo & HOW).
Ltac pz_open_rt RT :=
destruct RT as (LAWS & TL & TLF & ML & AMEMSET & AMEMCPY & ABCMP & ASM1 & SMP & ASF & FFL & KIND & HGM & HG15 & HIMGSH & HBC_RNG & HBC_VAL).
(* The frame f's premises, which the contract gives under 50 <= n: run it in a segment that has that. *)
Ltac pz_open_f Hbig :=
lazymatch goal with HFOK : 50 <= _ -> pz_fok _ _ _ _ _ _ _ _ _ |- _ =>
let H := fresh in pose proof (HFOK Hbig) as H; clear HFOK;
destruct H as (Hf0 & Hf47 & Hfam & Hfoimg & Hfsh & Hfwin & Hfpres & Hfloc & HRf & HHf & HGf & Hdfo) end.
Ltac pz_open_cur Hcur :=
destruct Hcur as (HEI & AGX & RF & E528 & E529 & HJ2 & KP).
(* The standard facts of a cut, under the names the walk tactics (pz_bases, pz_awr_hd, pz_win_tac) expect:
   run after pz_open, pz_open_rt and pz_open_cur. sp, sp1, F and FL become local definitions; the facts
   about the entry valuation E0 (pz_env) are EE, E10..E33, EFB, EOB, Usp, B10, B12, B33, B241..B308. *)
Ltac pz_std :=
let Hwx := fresh "Hwx" in let Hsegs := fresh "Hsegs" in let HBASE := fresh "HBASE" in let HBLO := fresh "HBLO" in
let C1 := fresh "C1" in let C2 := fresh "C2" in let C3 := fresh "C3" in let C4 := fresh "C4" in let C5 := fresh "C5" in
let WS := fresh "WS" in let Hes := fresh "Hes" in
let EE := fresh "EE" in let E10 := fresh "E10" in let E11 := fresh "E11" in let E12 := fresh "E12" in
let E32 := fresh "E32" in let E33 := fresh "E33" in let EFB := fresh "EFB" in let EOB := fresh "EOB" in
let HARc := fresh "HARc" in let Hfin2 := fresh "Hfin2" in let HfinS2 := fresh "HfinS2" in
let HFq := fresh "HFq" in let F := fresh "F" in let FL := fresh "FL" in let sp := fresh "sp" in let sp1 := fresh "sp1" in
let Hsp1r := fresh "Hsp1r" in let Hsp1al := fresh "Hsp1al" in let Hsp1al16 := fresh "Hsp1al16" in
let HFapp := fresh "HFapp" in let HFceil := fresh "HFceil" in let HFpres := fresh "HFpres" in let HFSpres := fresh "HFSpres" in
let HFimg := fresh "HFimg" in let N1 := fresh "N1" in let N2 := fresh "N2" in let N3 := fresh "N3" in let N4 := fresh "N4" in
let Hownf := fresh "Hownf" in
pose proof pa_wx as Hwx; pose proof pa_segs_low as Hsegs; pose proof pa_B_ok as HBASE; pose proof pa_base_lo as HBLO;
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5);
assert (WS : REAC_CTRL_PARSE_STK = 8336) by reflexivity; assert (Hes : ESTACK = 4096) by reflexivity;
match goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ ?own _ _ _ _ _ _ |- _ =>
lazymatch own with (1, _) :: _ => fail | _ =>
let HAR := fresh "HAR" in let Hpres := fresh "Hpres" in
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (?Hsp0al & ?Hstk0 & ?Hceil & ?Hslo & ?Hshi & ?H47 & ?Hbot & ?Htop2 & ?Htop) & _) end end;
lazymatch goal with H10 : getr ?regs 10 = _, H11 : getr _ 11 = _, H12 : getr _ 12 = _, Hflen : length ?fr = 50%nat |- _ =>
destruct (pz_env regs fr _ _ _ H10 H11 H12) as (EE & E10 & E11 & E12 & E32 & E33 & EFB & EOB) end;
lazymatch type of E10 with ew ?E0 10 = _ =>
let Usp := fresh "Usp" in assert (Usp : bv_unsigned (ew E0 2) = spZ _) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity) end;
lazymatch goal with HAR : AR _ _ ?lyc ?Sc ?W ?memc ?mdc, HJ : ajournal _ _ _ _ _ _ _ _ _ _ ?own ?lyc ?Sc _ _ _ _ |- _ =>
assert (Hownf : forall cid pos, In (cid, pos) own -> In (cid, pos) (frames Sc)) by
(let cid := fresh "cid" in let pos := fresh "pos" in let Hin := fresh "Hin" in let Hfrs := fresh "Hfrs" in
intros cid pos Hin; pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _); rewrite Hfrs;
apply in_or_app; left; exact Hin) end;
let X0 := fresh "X" in let X1 := fresh "X" in let X32 := fresh "X" in let X33 := fresh "X" in
pose proof (EOB 0%nat ltac:(lia)) as X0; pose proof (EOB 1%nat ltac:(lia)) as X1;
pose proof (EOB 66%nat ltac:(lia)) as X32; pose proof (EOB 67%nat ltac:(lia)) as X33;
lazymatch type of E10 with ew ?E0 10 = Z_to_bv 64 ?fv =>
lazymatch type of E12 with ew _ 12 = Z_to_bv 64 ?ov =>
lazymatch type of X0 with _ = Z_to_bv 64 ?v0 =>
lazymatch type of X1 with _ = Z_to_bv 64 ?v1 =>
lazymatch type of X32 with _ = Z_to_bv 64 ?v32 =>
lazymatch type of X33 with _ = Z_to_bv 64 ?v33 =>
assert (B241 : bv_unsigned (ew E0 241) = v0) by (change 241%nat with (A_OBJ 0); rewrite (EOB 0%nat ltac:(lia)); apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 0)); lia);
assert (B242 : bv_unsigned (ew E0 242) = v1) by (change 242%nat with (A_OBJ 1); rewrite (EOB 1%nat ltac:(lia)); apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 1)); lia);
assert (B307 : bv_unsigned (ew E0 307) = v32) by (change 307%nat with (A_OBJ 66); rewrite (EOB 66%nat ltac:(lia)); apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 66)); lia);
assert (B308 : bv_unsigned (ew E0 308) = v33) by (change 308%nat with (A_OBJ 67); rewrite (EOB 67%nat ltac:(lia)); apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 67)); lia);
assert (B10 : bv_unsigned (ew E0 10) = fv) by (rewrite E10; apply unsigned_lit_small; lia);
assert (B12 : bv_unsigned (ew E0 12) = ov) by (rewrite E12; apply unsigned_lit_small; lia) end end end end end end;
clear X0 X1 X32 X33;
pose proof (pa_obj_img 0 ltac:(unfold disco_nobj; lia)) as ?Hob0; pose proof (pa_obj_img 1 ltac:(unfold disco_nobj; lia)) as ?Hob1;
pose proof (pa_obj_img 66 ltac:(unfold disco_nobj; lia)) as ?Hob66; pose proof (pa_obj_img 67 ltac:(unfold disco_nobj; lia)) as ?Hob67;
lazymatch goal with HJ2 : ajournal _ _ _ _ _ _ _ _ _ _ ((1, ?fpos) :: _) ?lyc ?S2 _ _ _ _, Hfrs2 : frames ?S2 = (1, ?fpos) :: frames ?Sc,
  Eab : ablocks ?B ?lyc ?S2 = ablocks ?B ?lyc ?Sc, FFL : frame_flag_lawP _ _, LAWS : AR_laws _ ?B |- _ =>
pose proof (proj1 HJ2) as HARc;
assert (Hfin2 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity);
assert (HfinS2 : forall c p, In (c, p) (frames Sc) -> In (c, p) (frames S2)) by (intros c p Hcp; rewrite Hfrs2; right; exact Hcp);
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HARc Hfin2) as (?HFal & HFapp & HFpres & HFSpres);
destruct (frames_bounds _ B LAWS _ _ _ _ _ 1 fpos HARc Hfin2) as (?HF4096 & HFceil & _);
destruct (FFL _ _ _ _ _ 1 fpos HARc Hfin2) as (?HFLpres & ?HFLown & (?HFLapp & ?HFLimg) & (?HFL4096 & _ & ?HFLce));
pose proof (frm_off_imgP B _ _ _ _ _ 1 fpos HARc Hfin2) as HFimg;
change (fs_frame_bytes 1) with 128 in HFapp, HFceil, HFpres, HFSpres, HFimg;
change (128 / 8) with 16 in HFSpres;
set (F := frame_addr lyc 1 fpos) in *; set (FL := flag_addr lyc 1 fpos) in *;
assert (EF : F = frame_addr lyc 1 fpos) by reflexivity; assert (EFL : FL = flag_addr lyc 1 fpos) by reflexivity;
destruct (pz_nf_sep B LAWS lyc Sc S2 _ _ _ fpos F FL HARc Hfrs2 Eab EF EFL FFL) as (N1 & N2 & N3 & N4);
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia);
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity);
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia);
assert (HF8hi : F / 8 + 16 <= 17592184995840) by
(let Hd := fresh in assert (Hd : (F + 16 * 8) / 8 <= 140737479966720 / 8) by (apply Z.div_le_mono; lia);
rewrite Z.div_add in Hd by lia; change (140737479966720 / 8) with 17592184995840 in Hd; lia);
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp end;
lazymatch goal with Hal16 : spZ ?regs mod 16 = 0, Hwin : _ - _ <= spZ ?regs - REAC_CTRL_PARSE_STK |- _ =>
set (sp := spZ regs) in *; set (sp1 := pz_sp1 sp) in *;
destruct (sp1_facts (sp - 128) ltac:(lia) ltac:(rewrite <- Zminus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16);
change (32 * ((sp - 128) / 32)) with sp1 in Hsp1r, Hsp1al, Hsp1al16 end;
lazymatch type of E10 with ew ?E0 10 = _ =>
assert (B33 : bv_unsigned (ew E0 33) = sp1) by (rewrite E33; apply unsigned_lit_small; lia) end.
(* The opening of a cut, in the order a segment runs it (pz_open_f before pz_std: pz_std's B10 needs
   the bounds of f); checked here on a bare cut so that a change to the context cannot break it unseen. *)
Section t.
Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg disco_listing}.
Lemma pz_std_ok : forall B G, pz_rt B G -> forall c, pz_ok B c -> 50 <= cx_n c ->
forall E ms md, pz_cur B c E ms md -> True.
Proof.
intros B G RT c Hok Hbig E ms md Hcur.
pz_open c Hok. pz_open_rt RT. pz_open_cur Hcur. pz_open_f Hbig. pz_std. exact I.
Qed.
End t.
