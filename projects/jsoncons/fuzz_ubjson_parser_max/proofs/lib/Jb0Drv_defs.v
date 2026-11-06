(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX DrvKitA Jb0DrvEntry.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Jb0Drv_defs () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0Drv_defs."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."], [["1pair"; "1prod"; "2and"; "2ex"; "3Z"; "4wx_segs_nowrap"; "5IMG_CLIENT_A"; "5IMG_W_A"; "6loaded_segments"; "7In"; "8le"; "0hi"; "0hi'"; "0lo"; "0lo'"]]).
Definition STOPSA : list Z := [0x79190; 0x7918c; 0x77608; 0x62d08; 0x62d0c; 0x62d24; 0x62d34; 0x11575c; 0xa791c].
Definition FUELA : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].
Section FPX_1. Context {fx : PropExec.FPState}.
Definition runA (scr : scripts) (ss : sym_state) := sym_exec ASEGS FUELA true STOPSA scr ss [].
End FPX_1.
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
fst (fst (carry (s_log (fst (fst r))) kn [])).
Definition c_kept : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition IMG_CLIENT_A : list (Z * Z) :=
[(0x10000, 0x136000); (0x138ac0, 0x139380); (0x65f090, 0x670a68); (0x670a70, 0x670ab8); (0x670ad4, 0x670ae8); (0x670af0, 0x691f78);
(0x691f80, 0x693000)].
Definition IMG_W_A : list (Z * Z) :=
[(0x138ba8, 0x138ea0); (0x65f090, 0x670a68); (0x670a70, 0x670ab8); (0x670ad4, 0x670ae8); (0x670af0, 0x691f78); (0x691f80, 0x693000)].
Lemma img_client_rng : ltac2:(TCodec.tc2 tcn__Jb0Drv_defs "G'4&9'1%1233(0r2r1%347721&6%83621'2&:+RPP0r3%3221+Vb\P0%52;1%624<%8221%9251p0;1pHE1pLF1").
Proof. intros lo hi Hin. unfold IMG_CLIENT_A in Hin. cbn [In] in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]). destruct Hin. Qed.
Lemma img_w_sub : ltac2:(TCodec.tc2 tcn__Jb0Drv_defs "L'4&9'1%1233(0r2r1%347721&7%83621'3'2&6%<3:61&:r5%22;1r4%421<%8231%9271qJE1%<2F1qNG1%>2H1p0@1pHJ1pLK1").
Proof.
intros lo hi Hin. unfold IMG_W_A in Hin. cbn [In] in Hin.
destruct Hin as [E|[E|[E|[E|[E|[E|[]]]]]]]; injection E as <- <-;
[exists 0x138ac0, 0x139380 | exists 0x65f090, 0x670a68 | exists 0x670a70, 0x670ab8 | exists 0x670ad4, 0x670ae8
| exists 0x670af0, 0x691f78 | exists 0x691f80, 0x693000];
(split; [unfold IMG_CLIENT_A; cbn [In]; tauto | lia]).
Qed.
Definition IMG_RW_A : list (Z * Z) := [(0x65f090, 0x66f090)].
Definition keep_allocA (so sc : Z) (bls : list (nat * Z)) (vbnd : list (nat * Z)) (kn : list kentry) : list kentry :=
kn_keep 0 so sc bls vbnd [] IMG_CLIENT_A IMG_RW_A kn.
Definition MSO : Z := -128.
Definition kn_blkA (v : nat) (n : Z) : list kentry :=
[KRange (EVar v) 4096 (2 ^ 47 - 8388608 - n); KAlign (EVar v) 16; KWr (SA (EVar v) 0) n;
KDisj (SA (EVar 0) (-8388608)) 16777216 (SA (EVar v) 0) n;
KDisj (SA (ELit 0) 0x10000) 0x683000 (SA (EVar v) 0) n].
Lemma asegs_wx : ltac2:(TCodec.tc2 tcn__Jb0Drv_defs "3&5&8%211").
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Section FPX_2. Context {fx : PropExec.FPState}.
Definition ssA0 : sym_state := SS 0xa747c sr_mainA [] kn_mainA NX_MAIN.
Definition rA := Eval vm_compute in runA scr0 ssA0.
Definition srA : list expr := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA : list kentry := Eval vm_compute in kn_after rA kn_mainA.
Definition srB0 : list expr := sr_upd srA (ridx 10) (ELit 3).
Definition ssB0 : sym_state := SS 0x1277c0 srB0 [] knA NX_MAIN.
Definition rB := Eval vm_compute in runA scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knA.
Definition keepB : list kentry := Eval vm_compute in keep_allocA MSO 4096 [] [] knB.
Definition knC0 : list kentry := Eval vm_compute in kn_blkA 48 65536 ++ keepB.
Definition srC0 : list expr := sr_after_call_j srB (map ridx c_kept) 38.
Definition sumA (r : sym_state * list sidecond * scripts) := (s_pc (fst (fst r)), snd (fst r), s_next (fst (fst r)), s_log (fst (fst r))).
End FPX_2.
