(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore SegFastLoad.
Import ListNotations. Import AX2. Import AX2B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__SegFastCopy () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanCore.APC."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3.AX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3B.AX2B."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SegFastCopy.AX2Y."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SegFastCopy.AX2Y.Ctx3."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SegFastCopy.AX2Y.WithSegs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SegFastLoad.AX2L."], [["1bool"; "1list"; "1nat"; "1option"; "2eq"; "3Z"; "4Segment"; "5copy_facts"; "5copy_factsB"; "5kread8eB"; "6expr"; "6kentry"; "6lres"; "6sidecond"; "7know_lookupB"; "7mk_kix"]; ["7mkbc"; "9copy_facts3"; ":copy_facts2"; ":know_lookupB2"; ":kread8e2"; "8copy_facts2"; "8copy_factsM2"; ";mk_kix2"; "0acc"; "0b"; "0bc"; "0db"; "0dk"; "0fuel"; "0hints"; "0k"]; ["0kn"; "0kx"; "0kx2"; "0n"; "0off"; "0rb"; "0rk"; "0sb"; "0segs"; "0sk"; "0sx"]]).
Module AX2Y.
Section WithSegs.
Variable segs : list Segment.
Section Ctx.
Variable bc : bctx. Variable kx : kix. Variable kx2 : AX2L.kix2.
Definition know_lookupB2 (rb : expr) (rk : Z) (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
match AX2L.know_lookupA0I2 bc kx kx2 segs rb rk n sx hints acc with
| LMiss acc' hints' =>
match know_bytes_lit segs (bc_fk bc) rb rk n with
| Some bs => LHit (lit_of_bytes sx n bs) acc' hints'
| None => LMiss acc' hints'
end
| r => r
end.
Definition kread8e2 (b : expr) (off : Z) : option expr :=
match know_lookupB2 b off 8 false [] [] with
| LHit v [] _ => Some v
| _ => None
end.
Fixpoint copy_facts2 (fuel : nat) (sb : expr) (sk : Z) (db : expr) (dk : Z) (n : Z) : option (list kentry) :=
match fuel with
| O => Some []
| S f =>
if (Z.leb 8 n &&
match kread8e2 sb sk with Some _ => true | None => match APC.kread_bytesB segs bc 8 sb sk with Some _ => true | None => false end end)%bool then
match (match kread8e2 sb sk with
| Some v => Some v
| None => match APC.kread_bytesB segs bc 8 sb sk with
| Some bs => Some (ELit (zbytes_le_to_Z bs))
| None => None
end
end), copy_facts2 f sb (sk + 8) db (dk + 8) (n - 8) with
| Some v, Some rest => Some (KWord (SA db dk) 8 v :: rest)
| _, _ => None
end
else if Z.leb 1 n then
match know_lookupB2 sb sk 1 false [] [], copy_facts2 f sb (sk + 1) db (dk + 1) (n - 1) with
| LHit v [] _, Some rest => Some (KWord (SA db dk) 1 v :: rest)
| _, _ => None
end
else Some []
end.
End Ctx.
Lemma know_lookupB2_eq : ltac2:(TCodec.tc2 tcn__SegFastCopy "Q6'1';%211':'5'2'0%711'=%911'4'<&C&@r7%211&?%113&G%115r6r5r4r3r2r1%>9;97654321&>vQ8%281>987654%D3C41pQBF1pQNI1pRFK1pR8M1pR>O1pR<Q11pR2Q31").
Proof.
intros. unfold know_lookupB2, know_lookupB, know_lookupAB. rewrite AX2L.know_lookupA0I2_eq. reflexivity.
Qed.
Lemma kread8e2_eq : ltac2:(TCodec.tc2 tcn__SegFastCopy "J'1';%211':'5'4'3%114&D&@r3%211&?%113&G%115r2r1%:575321&9vQ8%241:54%A3?41pR:C1pQDE1pR2G1").
Proof. intros. unfold kread8e2, APC.kread8eB. rewrite know_lookupB2_eq. reflexivity. Qed.
Lemma copy_facts2_eq : ltac2:(TCodec.tc2 tcn__SegFastCopy "Q3'1';%211'2':'5'4'3%116&B&@r7%211&?%113&G%115r6r5r4r3r2r1%>9;97654321&8vQ8%281>987654%E3C41pR8G1pQJH1pQHJ1pRDJ1pR@L1pQLN1pR2Q01").
Proof.
intros kn fuel. induction fuel as [|f IH]; intros; [reflexivity|].
cbn [copy_facts2 APC.copy_factsB]. rewrite !kread8e2_eq, !know_lookupB2_eq, !IH. reflexivity.
Qed.
End WithSegs.
Section Ctx3.
Variable segs : list Segment.
Variable bc : bctx. Variable kx : kix. Variable kx2 : AX2L.kix2.
Fixpoint copy_facts3 (fuel : nat) (sb : expr) (sk : Z) (db : expr) (dk : Z) (n : Z) : option (list kentry) :=
match fuel with
| O => Some []
| S f =>
let bytewise (u : unit) :=
if Z.leb 1 n then
match know_lookupB2 segs bc kx kx2 sb sk 1 false [] [], copy_facts3 f sb (sk + 1) db (dk + 1) (n - 1) with
| LHit v [] _, Some rest => Some (KWord (SA db dk) 1 v :: rest)
| _, _ => None
end
else Some [] in
if Z.leb 8 n then
match (match kread8e2 segs bc kx kx2 sb sk with
| Some v => Some v
| None => match APC.kread_bytesB segs bc 8 sb sk with
| Some bs => Some (ELit (zbytes_le_to_Z bs))
| None => None
end
end) with
| Some v => match copy_facts3 f sb (sk + 8) db (dk + 8) (n - 8) with Some rest => Some (KWord (SA db dk) 8 v :: rest) | None => None end
| None => bytewise tt
end
else bytewise tt
end.
Lemma copy_facts3_eq : ltac2:(TCodec.tc2 tcn__SegFastCopy "N'2':'5'4'3'1';%211%411&Ar6r5r4r3r2r1%76654321&EvQ8vJvQ1vQ2%5:4321<;:987%D3?71pR8F1pQJG1pQHI1pRDI1pR@K1pQLM1").
Proof.
induction fuel as [|f IH]; intros; [reflexivity|]. cbn [copy_facts3 copy_facts2]. cbv zeta. rewrite !IH.
destruct (Z.leb 8 n); cbn [andb]; [|reflexivity].
destruct (kread8e2 segs bc kx kx2 sb sk) as [v|]; [reflexivity|].
destruct (APC.kread_bytesB segs bc 8 sb sk) as [bs|]; reflexivity.
Qed.
End Ctx3.
Definition copy_factsM2 (segs : list Segment) (fuel : nat) (k : list kentry) :=
copy_facts3 segs (mkbc k) (mk_kix k) (AX2L.mk_kix2 k) fuel.
Lemma copy_factsM2_eq : ltac2:(TCodec.tc2 tcn__SegFastCopy "F'4'1'6%211'2';%511':'5'3%114pR831pQJ41pQH61pRD61pR@81pR0:1pQL=1pRB?1&F&7%E3321").
Proof.
apply functional_extensionality; intros segs. apply functional_extensionality; intros fuel. apply functional_extensionality; intros k.
unfold copy_factsM2. repeat (apply functional_extensionality; intros ?). rewrite copy_facts3_eq, copy_facts2_eq, APC.copy_factsB_eqf'. reflexivity.
Qed.
End AX2Y.
