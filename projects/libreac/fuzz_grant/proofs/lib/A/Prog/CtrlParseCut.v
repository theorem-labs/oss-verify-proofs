(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: adapted from cgif's lib/A/ACgq.v (a walk's cut state) and lib/A/ACk8.v (the walk tactics) for reac_ctrl_parse of libreac's fuzz_grant: its contract, cuts and their tactics. *)
(* reac_ctrl_parse (0x82000) of fuzz_grant's ASan build: its contract (in the caller-journal form: it writes
   the caller's `struct reac_ctrl_parsed`) and the cuts its walk is split at. The walk (CtrlParse.v) goes from
   the entry to cut A (the side-stack frame taken); CtrlParseMid.v from cut A to cut B (after the bcmp
   wrapper) and, on the three header-rejecting paths, to cut J; CtrlParseTail.v from cut B to cut J;
   CtrlParseEpi.v from cut J (every path's join, 0x823a8) to the return. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import PaRun PaShadow PaJournal GrantSyms GrantList GrantPa GrantPaLib.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import GrantBase YC81 YC4b YC1g YC1h YC45 YC85 GrantFrame YC88.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import RcKind RcParse.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import CtrlParseLib KindOfLink1 GrantRo ACj1 GrantACja.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
(* Cut A, at 0x82074 (after __asan_stack_malloc_1 returns, the frame (1, fpos) seated): the state the
   walk reaches; CtrlParseMid.v starts here. *)
Definition ss_cutA : sstate := Eval vm_compute in
(mkSS 6596
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
      r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 274 0) |}]
    |};
    {|
      r_base := Some 274%nat;
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
      r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 273 0) |}]
    |};
    {|
      r_base := Some 273%nat;
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
        (10%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 3 |});
        (11%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |});
        (12%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 3 |});
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
rewrite ?(AGX 2%nat), ?(AGX 10%nat), ?(AGX 12%nat), ?(AGX 33%nat), ?(AGX 241%nat), ?(AGX 242%nat), ?(AGX 273%nat), ?(AGX 274%nat) by lia end;
lazymatch goal with
| Usp : bv_unsigned (ew ?E0 2) = _, B10 : bv_unsigned (ew ?E0 10) = _, B12 : bv_unsigned (ew ?E0 12) = _, B33 : bv_unsigned (ew ?E0 33) = _,
  B241 : bv_unsigned (ew ?E0 241) = _, B242 : bv_unsigned (ew ?E0 242) = _, B273 : bv_unsigned (ew ?E0 273) = _, B274 : bv_unsigned (ew ?E0 274) = _ |- _ =>
rewrite ?Usp, ?B10, ?B12, ?B33, ?B241, ?B242, ?B273, ?B274 end;
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
lazymatch goal with B12 : bv_unsigned (ew _ 12) = ?ov, HOW : forall a, _ -> awr_byte _ _ _ _ _ _ _ a, Eab : ablocks _ _ ?S2 = ablocks _ _ _ |- _ =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 12%nat ov); [reflexivity | pz_bases; lia | | ];
[ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; rewrite ?Eab; apply pz_awr_cons; apply HOW; lia | ] end
end.
Ltac pz_norm HS := lazymatch type of HS with st_ok_pi _ _ _ ?ss _ => let v := eval vm_compute in ss in change ss with v in HS end.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).
(* The image addresses this walk uses, each named once (fuzz_disco relocates them). *)
Definition A_ctrl_parseP : Z := BASE + AF_reac_ctrl_parse.
Definition OBJ_BCAST : nat := 15%nat.
(* The machine stack the call needs: its own 128-byte frame, realigned down to 32 bytes (at most 16 more),
   and below that 2 * ESTACK, which the bcmp wrapper's contract (abcmp_realizes) asks for; the other runtime
   entries and kind_of_link1 (KIND_OF_LINK1_STK = ESTACK) need less. *)
Definition TPARSE_STK : Z := 160 + 2 * ESTACK.
Section e.
Variable B : asyms.
Definition tctrl_parse_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
(lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
(regs : bvmap 5 word) (n o : Z) (fr : list byte) : world SEGS -> config -> Prop :=
fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k /\
aregs_preserved regs regs2 /\ frames S2 = frames Sc /\ ablocks B ly2 S2 = ablocks B lyc Sc /\ (exists ff, S2 = set_fs ff Sc) /\
getr regs2 10 = w64 (fst (ctrlparse n fr)) /\
(forall i, (i < 36)%nat -> aview SEGS (w_H W2) mem2 (o + Z.of_nat i) = Some (bv_unsigned (nth i (snd (ctrlparse n fr)) cp_z))) /\
acall_kept SEGS B lyc Sc W memc W2 mem2 (spZ regs - TPARSE_STK) (spZ regs) (fun a => o <= a < o + 36).
Definition tctrl_parse_spec : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) ch (f n o : Z) (fr : list byte),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 f -> getr regs 11 = w64 n -> getr regs 12 = w64 o -> 0 <= n < 2 ^ 64 ->
achain lyc (aview SEGS (w_H W) memc) (spZ regs) (s0Z regs) ch ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TPARSE_STK -> spZ regs <= sp0 ->
Z.of_nat (length (frames Sc)) <= 8 ->
afobj SEGS B lyc Sc W memc f 50 -> afobj SEGS B lyc Sc W memc o 36 -> f + 50 <= o \/ o + 36 <= f ->
(forall a, o <= a < o + 36 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
length fr = 50%nat ->
(forall i, (i < 50)%nat -> aview SEGS (w_H W) memc (f + Z.of_nat i) = Some (cp_v fr i)) ->
SRr SEGS W (cfg_at SEGS A_ctrl_parseP regs memc mdc)
(tctrl_parse_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs n o fr).
End e.
Definition PZspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* The stack region below the 128-byte frame, after the realignment of sp: it keeps the saved registers. *)
Definition pz_trim (rs : smem) : smem :=
map (fun r => match YP09.r_base r with
| Some 2%nat => YP09.mkRegion (Some 2%nat) (-96) 0 (-96) 0 (List.filter (fun c => -96 <=? YP09.c_off c) (YP09.r_chunks r))
| _ => r end) rs.
(* The static context of the walk once the frame is taken: the contract's premises, the two caller
   frames holding f and o, and the frame (1, fpos) of the post-allocation state S2. *)
Record pz_ctx : Type := mkPZ {
cx_STK : Z; cx_sp0 : Z; cx_FP : list (Z * Z); cx_ly : alayout; cx_S : astate; cx_W0 : world SEGS;
cx_mem0 : word -> option byte; cx_md0 : Model; cx_own : list (Z * Z); cx_lyc : alayout; cx_Sc : astate;
cx_W : world SEGS; cx_memc : word -> option byte; cx_mdc : Model; cx_k : Z; cx_regs : bvmap 5 word;
cx_ch : list (Z * Z * Z); cx_f : Z; cx_n : Z; cx_o : Z; cx_fr : list byte; cx_S2 : astate; cx_fpos : Z;
cx_cf : Z; cx_pf : Z; cx_co : Z; cx_po : Z }.
(* The runtime entries and the image facts the walk takes (an internal convention), one Prop. *)
Definition pz_rt (B : asyms) (G : list (Z * Z)) : Prop :=
AR_laws SEGS B /\ PALib B /\ PALibF B /\ model_laws (as_universe B) /\
aintrin_realizes SEGS B OSet (SIGMA GS___asan_memset) /\ aintrin_realizes SEGS B OCpy (SIGMA GS___asan_memcpy) /\
abcmp_realizes SEGS B (SIGMA GS___interceptor_trampoline_bcmp) /\ astack_malloc_realizes SEGS B 1 /\
stack_malloc_progressP B /\ astack_free_law SEGS B /\ frame_flag_lawP SEGS B /\ tkind_of_link1_spec B /\
globs_marked SEGS B G /\ In (VAL (A_OBJ OBJ_BCAST), 7) G /\ img_shadow_vis SEGS B /\
(IMG_LO + 64 <= VAL (A_OBJ OBJ_BCAST) /\ VAL (A_OBJ OBJ_BCAST) + 6 + 64 <= IMG_TOP) /\
(forall (H : word -> bool) mem, arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
forall i, 0 <= i < 6 -> aview SEGS H mem (VAL (A_OBJ OBJ_BCAST) + i) = Some 255).
Definition pz_ok (B : asyms) (c : pz_ctx) : Prop :=
ajournal SEGS B (cx_STK c) (cx_sp0 c) (cx_FP c) (cx_ly c) (cx_S c) (cx_W0 c) (cx_mem0 c) (cx_md0 c) (cx_own c) (cx_lyc c) (cx_Sc c) (cx_W c) (cx_memc c) (cx_mdc c) (cx_k c) /\
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H (cx_W c)) (cx_memc c)) /\
YK0s.ret_ok (getr (cx_regs c) 1) /\ 4096 <= raZ (cx_regs c) /\
getr (cx_regs c) 3 = w64 (as_gp B) /\ getr (cx_regs c) 4 = w64 (as_tp B) /\
getr (cx_regs c) 10 = w64 (cx_f c) /\ getr (cx_regs c) 11 = w64 (cx_n c) /\ getr (cx_regs c) 12 = w64 (cx_o c) /\ 0 <= (cx_n c) < 2 ^ 64 /\
achain (cx_lyc c) (aview SEGS (w_H (cx_W c)) (cx_memc c)) (spZ (cx_regs c)) (s0Z (cx_regs c)) (cx_ch c) /\
spZ (cx_regs c) mod 16 = 0 /\ (cx_sp0 c) - (cx_STK c) <= spZ (cx_regs c) - TPARSE_STK /\ spZ (cx_regs c) <= (cx_sp0 c) /\
Z.of_nat (length (frames (cx_Sc c))) <= 8 /\
afobj SEGS B (cx_lyc c) (cx_Sc c) (cx_W c) (cx_memc c) (cx_f c) 50 /\ afobj SEGS B (cx_lyc c) (cx_Sc c) (cx_W c) (cx_memc c) (cx_o c) 36 /\ ((cx_f c) + 50 <= (cx_o c) \/ (cx_o c) + 36 <= (cx_f c)) /\
(forall a, (cx_o c) <= a < (cx_o c) + 36 -> awr_byte (cx_STK c) (cx_sp0 c) (cx_FP c) (ablocks B (cx_ly c) (cx_S c)) (ablocks B (cx_lyc c) (cx_Sc c)) (cx_lyc c) (cx_own c) a) /\
length (cx_fr c) = 50%nat /\
(forall i, (i < 50)%nat -> aview SEGS (w_H (cx_W c)) (cx_memc c) ((cx_f c) + Z.of_nat i) = Some (cp_v (cx_fr c) i)) /\
In ((cx_cf c), (cx_pf c)) (frames (cx_Sc c)) /\ frame_addr (cx_lyc c) (cx_cf c) (cx_pf c) <= (cx_f c) /\ (cx_f c) + 50 <= frame_addr (cx_lyc c) (cx_cf c) (cx_pf c) + fs_frame_bytes (cx_cf c) /\
In ((cx_co c), (cx_po c)) (frames (cx_Sc c)) /\ frame_addr (cx_lyc c) (cx_co c) (cx_po c) <= (cx_o c) /\ (cx_o c) + 36 <= frame_addr (cx_lyc c) (cx_co c) (cx_po c) + fs_frame_bytes (cx_co c) /\
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
acall_kept SEGS B (cx_lyc c) (cx_Sc c) (cx_W c) (cx_memc c) (cx_W c) (ms_mem ms) (spZ (cx_regs c) - TPARSE_STK) (spZ (cx_regs c)) (fun a => (cx_o c) <= a < (cx_o c) + 36).
Definition pz_post (B : asyms) (c : pz_ctx) : world SEGS -> config -> Prop :=
tctrl_parse_post B (cx_STK c) (cx_sp0 c) (cx_FP c) (cx_ly c) (cx_S c) (cx_W0 c) (cx_mem0 c) (cx_md0 c) (cx_own c) (cx_lyc c) (cx_Sc c) (cx_W c) (cx_memc c) (cx_k c) (cx_regs c) (cx_n c) (cx_o c) (cx_fr c).
(* Cut J (0x823a8): a0 (atom 700) is the return code and the out struct holds the model's 36 bytes. *)
Definition pz_cutJ_spec (B : asyms) (c : pz_ctx) : Prop :=
forall E ms md, pz_cur B c E ms md ->
st_ok_pi SEGS VAL E ss_cutJ (restrict (w_H (cx_W c)) ms) ->
ew E 700 = Z_to_bv 64 (fst (ctrlparse (cx_n c) (cx_fr c))) ->
(forall i, (i < 36)%nat -> aview SEGS (w_H (cx_W c)) (ms_mem ms) (cx_o c + Z.of_nat i) =
Some (bv_unsigned (nth i (snd (ctrlparse (cx_n c) (cx_fr c))) cp_z))) ->
SRr SEGS (cx_W c) (mkCfg ms md) (pz_post B c).
(* Cut B (0x821c8): the header was accepted; atom 640 is the bcmp wrapper's result. *)
Definition pz_cutB_spec (B : asyms) (c : pz_ctx) : Prop :=
forall E ms md, pz_cur B c E ms md ->
st_ok_pi SEGS VAL E ss_cutB (restrict (w_H (cx_W c)) ms) ->
sh_ok SEGS PZx PZ_SH E (mrestrict (w_H (cx_W c)) (ms_mem ms)) ->
cp_hdr (cx_n c) (cx_fr c) = true ->
(ew E 640 = Z_to_bv 64 0 <-> cp_bcast (cx_fr c) = true) ->
SRr SEGS (cx_W c) (mkCfg ms md) (pz_post B c).
(* Cut M (0x82140): the memset of the out struct returned; MidNone (CtrlParseNone.v) takes the paths the
   header check rejects, MidAcc (CtrlParseAcc.v) the accepting path. *)
Definition pz_cutM_case (B : asyms) (c : pz_ctx) (P : Prop) : Prop :=
forall E ms md, pz_cur B c E ms md ->
st_ok_pi SEGS VAL E ss_cutM (restrict (w_H (cx_W c)) ms) ->
sh_ok SEGS PZx PZ_SH E (mrestrict (w_H (cx_W c)) (ms_mem ms)) ->
P ->
SRr SEGS (cx_W c) (mkCfg ms md) (pz_post B c).
(* Cut B restricted to the frames of one class of frame type and link (CtrlParseTail1..5.v). *)
Definition pz_cutB_case (B : asyms) (c : pz_ctx) (P : list byte -> Prop) : Prop :=
forall E ms md, pz_cur B c E ms md ->
st_ok_pi SEGS VAL E ss_cutB (restrict (w_H (cx_W c)) ms) ->
sh_ok SEGS PZx PZ_SH E (mrestrict (w_H (cx_W c)) (ms_mem ms)) ->
cp_hdr (cx_n c) (cx_fr c) = true ->
(ew E 640 = Z_to_bv 64 0 <-> cp_bcast (cx_fr c) = true) ->
P (cx_fr c) ->
SRr SEGS (cx_W c) (mkCfg ms md) (pz_post B c).
(* Cut A (0x82074): the frame (1, fpos) is seated. *)
Definition pz_cutA_spec (B : asyms) (c : pz_ctx) : Prop :=
forall E ms md, pz_cur B c E ms md ->
st_ok_pi SEGS VAL E ss_cutA (restrict (w_H (cx_W c)) ms) ->
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
destruct c as [STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch f n o fr S2 fpos cf pf co po];
unfold pz_ok, pz_cur, pz_post, pz_E0, pz_cutJ_spec, pz_cutB_spec, pz_cutM_case, pz_cutB_case, pz_cutA_spec in *;
cbn [pz_ok pz_cur pz_post pz_E0 cx_STK cx_sp0 cx_FP cx_ly cx_S cx_W0 cx_mem0 cx_md0 cx_own cx_lyc cx_Sc cx_W cx_memc
cx_mdc cx_k cx_regs cx_ch cx_f cx_n cx_o cx_fr cx_S2 cx_fpos cx_cf cx_pf cx_co cx_po] in *;
destruct Hok as (HJ & HROD & Hra & Hra4 & Hgp & Htp & H10 & H11 & H12 & Hn & Hch & Hal16 & Hwin & Hsp0 & Hroom &
Hof & Hoo & Hdfo & HOW & Hflen & Hfr & Hfin & Hflo & Hfhi & Hoin & Holo & Hohi & Hfrs2 & Eab & Hnin & ES2).
Ltac pz_open_rt RT :=
destruct RT as (LAWS & TL & TLF & ML & AMEMSET & AMEMCPY & ABCMP & ASM1 & SMP & ASF & FFL & KIND & HGM & HG15 & HIMGSH & HBC_RNG & HBC_VAL).
Ltac pz_open_cur Hcur :=
destruct Hcur as (HEI & AGX & RF & E528 & E529 & HJ2 & KP).
(* The standard facts of a cut, under the names the walk tactics (pz_bases, pz_awr_hd, pz_win_tac) expect:
   run after pz_open, pz_open_rt and pz_open_cur. sp, sp1, F and FL become local definitions; the facts
   about the entry valuation E0 (pz_env) are EE, E10..E33, EFB, EOB, Usp, B10, B12, B33, B241..B274. *)
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
let HFimg := fresh "HFimg" in let HsepF := fresh "HsepF" in let HsepO := fresh "HsepO" in
pose proof pa_wx as Hwx; pose proof pa_segs_low as Hsegs; pose proof pa_B_ok as HBASE; pose proof pa_base_lo as HBLO;
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5);
assert (WS : TPARSE_STK = 8352) by reflexivity; assert (Hes : ESTACK = 4096) by reflexivity;
match goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ ?own _ _ _ _ _ _ |- _ =>
lazymatch own with (1, _) :: _ => fail | _ =>
let HAR := fresh "HAR" in let Hpres := fresh "Hpres" in
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (?Hsp0al & ?Hstk0 & ?Hceil & ?Hslo & ?Hshi & ?H47 & ?Hbot & ?Htop2 & ?Htop) & _) end end;
lazymatch goal with H10 : getr ?regs 10 = _, H11 : getr _ 11 = _, H12 : getr _ 12 = _, Hflen : length ?fr = 50%nat |- _ =>
destruct (pz_env regs fr _ _ _ H10 H11 H12) as (EE & E10 & E11 & E12 & E32 & E33 & EFB & EOB) end;
lazymatch type of E10 with ew ?E0 10 = _ =>
let Usp := fresh "Usp" in assert (Usp : bv_unsigned (ew E0 2) = spZ _) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity) end;
lazymatch goal with Hof : afobj _ _ _ _ _ _ ?f 50, Hoo : afobj _ _ _ _ _ _ ?o 36 |- _ =>
pose proof Hof as (_ & ?Hf8 & ?HRf); pose proof Hoo as (_ & ?Ho8 & ?HRo) end;
lazymatch goal with Hfin : In (?cf, ?pf) (frames ?Sc), Hoin : In (?co, ?po) (frames ?Sc), HAR : AR _ _ ?lyc ?Sc ?W ?memc ?mdc,
  LAWS : AR_laws _ ?B |- _ =>
destruct (frames_bounds _ B LAWS lyc Sc W memc mdc cf pf HAR Hfin) as (?Hf4096 & ?Hfceil & ?Hfapp);
destruct (frames_bounds _ B LAWS lyc Sc W memc mdc co po HAR Hoin) as (?Ho4096 & ?Hoceil & ?Hoapp);
pose proof (frm_off_imgP B lyc Sc W memc mdc cf pf HAR Hfin) as ?Hcfimg;
pose proof (frm_off_imgP B lyc Sc W memc mdc co po HAR Hoin) as ?Hcoimg end;
let X0 := fresh "X" in let X1 := fresh "X" in let X32 := fresh "X" in let X33 := fresh "X" in
pose proof (EOB 0%nat ltac:(lia)) as X0; pose proof (EOB 1%nat ltac:(lia)) as X1;
pose proof (EOB 32%nat ltac:(lia)) as X32; pose proof (EOB 33%nat ltac:(lia)) as X33;
lazymatch type of E10 with ew ?E0 10 = Z_to_bv 64 ?fv =>
lazymatch type of E12 with ew _ 12 = Z_to_bv 64 ?ov =>
lazymatch type of X0 with _ = Z_to_bv 64 ?v0 =>
lazymatch type of X1 with _ = Z_to_bv 64 ?v1 =>
lazymatch type of X32 with _ = Z_to_bv 64 ?v32 =>
lazymatch type of X33 with _ = Z_to_bv 64 ?v33 =>
assert (B241 : bv_unsigned (ew E0 241) = v0) by (change 241%nat with (A_OBJ 0); rewrite (EOB 0%nat ltac:(lia)); apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 0)); lia);
assert (B242 : bv_unsigned (ew E0 242) = v1) by (change 242%nat with (A_OBJ 1); rewrite (EOB 1%nat ltac:(lia)); apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 1)); lia);
assert (B273 : bv_unsigned (ew E0 273) = v32) by (change 273%nat with (A_OBJ 32); rewrite (EOB 32%nat ltac:(lia)); apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 32)); lia);
assert (B274 : bv_unsigned (ew E0 274) = v33) by (change 274%nat with (A_OBJ 33); rewrite (EOB 33%nat ltac:(lia)); apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 33)); lia);
assert (B10 : bv_unsigned (ew E0 10) = fv) by (rewrite E10; apply unsigned_lit_small; lia);
assert (B12 : bv_unsigned (ew E0 12) = ov) by (rewrite E12; apply unsigned_lit_small; lia) end end end end end end;
clear X0 X1 X32 X33;
pose proof (pa_obj_img 0 ltac:(lia)) as ?Hob0; pose proof (pa_obj_img 1 ltac:(lia)) as ?Hob1;
pose proof (pa_obj_img 32 ltac:(lia)) as ?Hob32; pose proof (pa_obj_img 33 ltac:(lia)) as ?Hob33;
lazymatch goal with HJ2 : ajournal _ _ _ _ _ _ _ _ _ _ ((1, ?fpos) :: _) ?lyc ?S2 _ _ _ _, Hfrs2 : frames ?S2 = (1, ?fpos) :: frames ?Sc,
  Hfin : In (?cf, ?pf) (frames ?Sc), Hoin : In (?co, ?po) (frames ?Sc), FFL : frame_flag_lawP _ _, LAWS : AR_laws _ ?B |- _ =>
pose proof (proj1 HJ2) as HARc;
assert (Hfin2 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity);
assert (HfinS2 : forall c p, In (c, p) (frames Sc) -> In (c, p) (frames S2)) by (intros c p Hcp; rewrite Hfrs2; right; exact Hcp);
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HARc Hfin2) as (?HFal & HFapp & HFpres & HFSpres);
destruct (frames_bounds _ B LAWS _ _ _ _ _ 1 fpos HARc Hfin2) as (?HF4096 & HFceil & _);
destruct (FFL _ _ _ _ _ 1 fpos HARc Hfin2) as (?HFLpres & ?HFLown & (?HFLapp & ?HFLimg) & (?HFL4096 & _ & ?HFLce));
pose proof (frm_off_imgP B _ _ _ _ _ 1 fpos HARc Hfin2) as HFimg;
pose proof (pz_own_sep B LAWS _ _ _ _ _ 1 fpos Sc cf pf HARc Hfrs2 Hfin) as HsepF;
pose proof (pz_own_sep B LAWS _ _ _ _ _ 1 fpos Sc co po HARc Hfrs2 Hoin) as HsepO;
unfold zdisjoint, frame_rng in HsepF, HsepO; cbn [fst snd] in HsepF, HsepO;
change (fs_frame_bytes 1) with 128 in HFapp, HFceil, HFpres, HFSpres, HFimg, HsepF, HsepO;
change (128 / 8) with 16 in HFSpres;
set (F := frame_addr lyc 1 fpos) in *; set (FL := flag_addr lyc 1 fpos) in *;
assert (EF : F = frame_addr lyc 1 fpos) by reflexivity; assert (EFL : FL = flag_addr lyc 1 fpos) by reflexivity;
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia);
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity);
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia);
assert (HF8hi : F / 8 + 16 <= 17592184995840) by
(let Hd := fresh in assert (Hd : (F + 16 * 8) / 8 <= 140737479966720 / 8) by (apply Z.div_le_mono; lia);
rewrite Z.div_add in Hd by lia; change (140737479966720 / 8) with 17592184995840 in Hd; lia);
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp end;
lazymatch goal with Hal16 : spZ ?regs mod 16 = 0, Hwin : _ - _ <= spZ ?regs - TPARSE_STK |- _ =>
set (sp := spZ regs) in *; set (sp1 := pz_sp1 sp) in *;
destruct (sp1_facts (sp - 128) ltac:(lia) ltac:(rewrite <- Zminus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16);
change (32 * ((sp - 128) / 32)) with sp1 in Hsp1r, Hsp1al, Hsp1al16 end;
lazymatch type of E10 with ew ?E0 10 = _ =>
assert (B33 : bv_unsigned (ew E0 33) = sp1) by (rewrite E33; apply unsigned_lit_small; lia) end.
