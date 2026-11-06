(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac HeapIface.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_RepCrt () : Init.string Init.list := ["Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C4"; "WithSegs.co_ob"; "WithSegs.cj0"; "WithSegs.cj_rawtag"; "WithSegs.cj1"; "OSSVerify.KrLib.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "WithSegs.co_rawlen"; "WithSegs.co_rawp"; "OSSVerify.KrLib.Lib.Cells.CB"; "WithSegs.cj2"; "WithSegs.co_issuer_next"; "WithSegs.cj3"; "WithSegs.co_subject_next"; "WithSegs.cj4"; "WithSegs.co_pkinfo"; "WithSegs.co_pkctx"; "WithSegs.cj5"; "WithSegs.co_san_next"; "WithSegs.cj6"; "WithSegs.co_akid_next"; "WithSegs.cj7"; "WithSegs.co_pol_next"; "WithSegs.cj8"; "WithSegs.co_eku_next"; "WithSegs.cj9"; "WithSegs.co_sigopts"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Datatypes.app"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "WithSegs.co_pkowned"; "WithSegs.oblk"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.pair"; "OSSVerify.KrLib.Spec.Rep.NAME_SIZE"; "WithSegs.co_issuer"; "WithSegs.co_subject"; "OSSVerify.KrLib.Spec.Rep.SEQ_SIZE"; "WithSegs.co_eku"; "WithSegs.co_san"; "WithSegs.co_pol"; "WithSegs.co_akid"; "Corelib.Init.Logic.and"; "OSSVerify.KrLib.Spec.Rep.name_chain"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.True"; "OSSVerify.KrLib.Spec.Rep.seq_chain"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.eq"; "Stdlib.Lists.List.In"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "Stdlib.ZArith.BinInt.Z.to_nat"; "WithSegs.cj_raw"; "pk_rep"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.Lists.List.NoDup"; "Corelib.Init.Datatypes.fst"; "WithSegs.crt_blocks"; "WithSegs.crt_cells"; "Stdlib.ZArith.BinInt.Z.modulo"; "WithSegs.CRT_SIZE"; "Stdlib.ZArith.BinInt.Z.pow"; "WithSegs.crt_own_ok"; "WithSegs.CRJ"; "zeros"; "stdpp.bitvector.definitions.bv"; "WithSegs.sj0"; "OSSVerify.KrLib.Lib.Cells.C1"; "WithSegs.sj_merged"; "WithSegs.sj1"; "WithSegs.sj2"; "WithSegs.pj_rawtag"; "WithSegs.pj0"; "WithSegs.po_rawlen"; "WithSegs.po_rawp"; "WithSegs.pj1"; "WithSegs.po_crt"; "WithSegs.pj_crt"; "WithSegs.pj2"; "WithSegs.pj3"; "WithSegs.signer_cells"; "WithSegs.po_issuer0_next"; "WithSegs.po_signers_next"; "WithSegs.pj_s0"; "WithSegs.po_names0"; "WithSegs.signer_blocks"; "WithSegs.po_signers"; "WithSegs.pkcs7_cells"; "WithSegs.PKCS7_SIZE"; "WithSegs.pj_raw"; "WithSegs.signer_chain"; "WithSegs.p7_blocks"].


Definition zeros (n : nat) : list byte := repeat (Z_to_bv 8 0) n.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record pk_class (segs : list Segment) := PKC {
  pk_rep : mem -> list blk -> Z -> Z -> Z -> list blk -> Prop;
  (* [comment removed for export] *)
  pk_rep_null : forall m LB PKA, pk_rep m LB PKA 0 0 [];
  pk_rep_null_inv : forall m LB PKA ctx owned, pk_rep m LB PKA 0 ctx owned -> owned = [];
  (* [comment removed for export] *)
  pk_rep_blocks : forall m LB PKA info ctx owned, pk_rep m LB PKA info ctx owned -> forall b, In b owned -> In b LB;
  (* [comment removed for export] *)
  pk_rep_frame : forall m m' LB LB' PKA info ctx owned,
      pk_rep m LB PKA info ctx owned ->
      mem_inv segs m' ->
      (forall b, In b owned -> In b LB') ->
      (forall a, in_block owned a -> m' (wa a) = m (wa a)) ->
      pk_rep m' LB' PKA info ctx owned
}.

Section WithSegs.
Variable segs : list Segment.
Variable PK : pk_class segs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record crt_own := CRT {
  co_ob : word;          (* [comment removed for export] *)
  co_rawlen : Z; co_rawp : Z;
  co_issuer_next : Z; co_issuer : list Z;      (* [comment removed for export] *)
  co_subject_next : Z; co_subject : list Z;
  co_pkinfo : Z; co_pkctx : Z; co_pkowned : list blk;
  co_san_next : Z; co_san : list Z;            (* [comment removed for export] *)
  co_akid_next : Z; co_akid : list Z;
  co_pol_next : Z; co_pol : list Z;
  co_eku_next : Z; co_eku : list Z;
  co_sigopts : Z
}.

(* [comment removed for export] *)
Record crt_junk := CRJ {
  cj0 : word; cj_rawtag : word; cj1 : word;
  cj2 : list byte;   (* [comment removed for export] *)
  cj3 : list byte;   (* [comment removed for export] *)
  cj4 : list byte;   (* [comment removed for export] *)
  cj5 : list byte;   (* [comment removed for export] *)
  cj6 : list byte;   (* [comment removed for export] *)
  cj7 : list byte;   (* [comment removed for export] *)
  cj8 : list byte;   (* [comment removed for export] *)
  cj9 : list byte;   (* [comment removed for export] *)
  cj_raw : list byte (* [comment removed for export] *)
}.

Definition CRT_SIZE : Z := 744.

Definition crt_cells (f : crt_own) (j : crt_junk) : list cell := ltac2:(CDefT.buildp (gd_tbl_RepCrt ()) "(0.$1.(2.(3.O2.))(0.$1.(2.(4.O1.))(0.$1.(2.(5.O1.))(0.$1.(2.(6.O1.))(0.$1.(7.(8.&40.(9.O2.)))(0.$1.(7.(8.&40.(:.O2.)))(0.$1.(;.#;0.(<.O1.))(0.$1.(7.(8.&40.(=.O2.)))(0.$1.(;.#38.(>.O1.))(0.$1.(7.(8.&40.(?.O2.)))(0.$1.(;.#50.(10.O1.))(0.$1.(7.(8.&40.(11.O2.)))(0.$1.(7.(8.&40.(12.O2.)))(0.$1.(;.#60.(13.O1.))(0.$1.(7.(8.&40.(14.O2.)))(0.$1.(;.#48.(15.O1.))(0.$1.(7.(8.&40.(16.O2.)))(0.$1.(;.#48.(17.O1.))(0.$1.(7.(8.&40.(18.O2.)))(0.$1.(;.#28.(19.O1.))(0.$1.(7.(8.&40.(1:.O2.)))(0.$1.(;.#28.(1;.O1.))(0.$1.(7.(8.&40.(1<.O2.)))(0.$1.(7.(8.&40.=))(1=.$1.)))))))))))))))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition oblk (a n : Z) : list blk := if a =? 0 then [] else [(a, n)].
Definition crt_blocks (f : crt_own) : list blk := ltac2:(CDefT.buildp (gd_tbl_RepCrt ()) "(1>.$1?.(20.O1.)(1>.$1?.(21.(1<.O1.)+8.)(1>.(22.$23.$23.)(24.$23.(22.$23.$23.)La,$23.(25.$23.$23.R1.$26.)(27.O1.))(1>.(22.$23.$23.)(24.$23.(22.$23.$23.)La,$23.(25.$23.$23.R1.$26.)(28.O1.))(1>.(22.$23.$23.)(24.$23.(22.$23.$23.)La,$23.(25.$23.$23.R1.$29.)(2:.O1.))(1>.(22.$23.$23.)(24.$23.(22.$23.$23.)La,$23.(25.$23.$23.R1.$29.)(2;.O1.))(1>.(22.$23.$23.)(24.$23.(22.$23.$23.)La,$23.(25.$23.$23.R1.$29.)(2<.O1.))(1>.(22.$23.$23.)(24.$23.(22.$23.$23.)La,$23.(25.$23.$23.R1.$29.)(2=.O1.))(21.(:.O1.)(9.O1.))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition crt_own_ok (m : mem) (LB : list blk) (A : Z) (f : crt_own) (j : crt_junk) : Prop := ltac2:(CDefT.buildp (gd_tbl_RepCrt ()) "(2>.(2?.Vsegs,L,(30.$1.)$31.O5.O4.(=.O2.)(27.O2.))(2>.(2?.Vsegs,L,(30.$1.)$31.O5.O4.(?.O2.)(28.O2.))(2>.(32.Vsegs,L,(30.$1.)$31.O5.O4.(14.O2.)(2;.O2.))(2>.(32.Vsegs,L,(30.$1.)$31.O5.O4.(16.O2.)(2=.O2.))(2>.(32.Vsegs,L,(30.$1.)$31.O5.O4.(18.O2.)(2<.O2.))(2>.(32.Vsegs,L,(30.$1.)$31.O5.O4.(1:.O2.)(2:.O2.))(2>.(33.(34.$23.(1<.O2.)=)(2>.(35.(22.$23.$23.)(25.$23.$23.(1<.O2.)+8.)O4.)(36.=(1<.O2.))))(2>.(33.(34.$23.(:.O2.)=)(2>.(35.(22.$23.$23.)(25.$23.$23.(:.O2.)(9.O2.))O4.)(2>.(37.=(9.O2.))(38.Vsegs,O5.(:.O2.)(0.$1.(;.(39.(9.O2.))(3:.O1.))(1=.$1.))))))(2>.(3;.Vsegs,VPK,O5.O4.(3<.O3.+168.)(11.O2.)(12.O2.)(20.O2.))(3=.$23.(24.(22.$23.$23.)$23.(3>.$23.$23.)(3?.O2.))))))))))))")
(* [comment removed for export] *).

Definition crt_at (m : mem) (LB : list blk) (A : Z) (f : crt_own) (j : crt_junk) : Prop := ltac2:(CDefT.buildp (gd_tbl_RepCrt ()) "(2>.(38.Vsegs,O5.O3.(40.O2.O1.))(2>.(34.$23.(41.O3.+8.)=)(2>.(36.=O3.)(2>.(37.(3<.O3.$42.)(43.+2.+40.))(44.O5.O4.O3.O2.O1.)))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition crt_own_zero : crt_own := CRT (Z_to_bv 64 0) 0 0 0 [] 0 [] 0 0 [] 0 [] 0 [] 0 [] 0 [] 0.
Definition crt_junk_zero : crt_junk := ltac2:(CDefT.buildp (gd_tbl_RepCrt ()) "(45.(8.&40.=)(8.&40.=)(8.&40.=)(46.#;0.)(46.#38.)(46.#50.)(46.#60.)(46.#48.)(46.#48.)(46.#28.)(46.#28.)(1=.(47.&8.)))")
(* [comment removed for export] *).
Definition crt_zero (m : mem) (A : Z) : Prop := rw_cells segs m A [CB 744 (zeros 744)].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition CRL_SIZE : Z := 416.
Definition crl_zero (m : mem) (A : Z) : Prop := rw_cells segs m A [CB 416 (zeros 416)].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SIGNER_SIZE : Z := 200.

Record signer_junk := SGJ {
  sj0 : list byte;   (* [comment removed for export] *)
  sj_merged : byte; sj1 : list byte;  (* [comment removed for export] *)
  sj2 : list byte    (* [comment removed for export] *)
}.
Definition signer_cells (issuer_next nxt : Z) (j : signer_junk) : list cell := ltac2:(CDefT.buildp (gd_tbl_RepCrt ()) "(0.$1.(;.#50.(48.O1.))(0.$1.(7.(8.&40.O3.))(0.$1.(49.(4:.O1.))(0.$1.(;.#7.(4;.O1.))(0.$1.(;.#60.(4<.O1.))(0.$1.(7.(8.&40.O2.))(1=.$1.)))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Fixpoint signer_chain (m : mem) (LB : list blk) (a : Z) (l : list (Z * list Z)) {struct l} : Prop :=
  match l with
  | [] => a = 0
  | (a', names) :: r => a = a' /\ In (a, SIGNER_SIZE) LB /\ a mod 16 = 0 /\ 0 < a
      /\ exists (inext nxt : Z) (j : signer_junk),
           rw_cells segs m a (signer_cells inext nxt j)
           /\ name_chain segs (fun _ => True) m LB inext names
           /\ signer_chain m LB nxt r
  end.

(* [comment removed for export] *)
Fixpoint signer_blocks (l : list (Z * list Z)) : list blk :=
  match l with
  | [] => []
  | e :: r => (map (fun a => (a, NAME_SIZE)) (snd e) ++ [(fst e, SIGNER_SIZE)]) ++ signer_blocks r
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PKCS7_SIZE : Z := 1440.

Record p7_own := P7O {
  po_rawlen : Z; po_rawp : Z;
  po_crt : crt_own;
  po_issuer0_next : Z; po_names0 : list Z;        (* [comment removed for export] *)
  po_signers_next : Z; po_signers : list (Z * list Z)
}.
Record p7_junk := P7J {
  pj_rawtag : word; pj0 : word;
  pj1 : list byte;   (* [comment removed for export] *)
  pj_crt : crt_junk;
  pj2 : list byte;   (* [comment removed for export] *)
  pj3 : list byte;   (* [comment removed for export] *)
  pj_s0 : signer_junk;
  pj_raw : list byte (* [comment removed for export] *)
}.

Definition pkcs7_cells (po : p7_own) (j : p7_junk) : list cell := ltac2:(CDefT.buildp (gd_tbl_RepCrt ()) "(1>.$1.(0.$1.(2.(4=.O1.))(0.$1.(2.(4>.O1.))(0.$1.(7.(8.&40.(4?.O2.)))(0.$1.(7.(8.&40.(50.O2.)))(0.$1.(;.#28.(51.O1.))(1=.$1.))))))(1>.$1.(40.(52.O2.)(53.O1.))(1>.$1.(0.$1.(;.#8.(54.O1.))(0.$1.(;.#1:0.(46.#1:0.))(0.$1.(;.#8.(55.O1.))(1=.$1.))))(56.(57.O2.)(58.O2.)(59.O1.)))))")
(* [comment removed for export] *).

Definition p7_blocks (po : p7_own) : list blk := ltac2:(CDefT.buildp (gd_tbl_RepCrt ()) "(1>.(22.$23.$23.)(0.(22.$23.$23.)(25.$23.$23.(50.O1.)(4?.O1.))(1=.(22.$23.$23.)))(1>.$1?.(3?.(52.O1.))(1>.(22.$23.$23.)(24.$23.(22.$23.$23.)La,$23.(25.$23.$23.R1.$26.)(5:.O1.))(5;.(5<.O1.)))))")
(* [comment removed for export] *).

Definition pkcs7_zero (m : mem) (A : Z) : Prop := rw_cells segs m A [CB 1440 (zeros 1440)].

(* [comment removed for export] *)
Definition pkcs7_live (m : mem) (LB : list blk) (A : Z) (po : p7_own) (j : p7_junk) : Prop := ltac2:(CDefT.buildp (gd_tbl_RepCrt ()) "(2>.(38.Vsegs,O5.O3.(5=.O2.O1.))(2>.(34.$23.(41.O3.+8.)=)(2>.(36.=O3.)(2>.(37.(3<.O3.$5>.)(43.+2.+40.))(2>.(36.=(50.O2.))(2>.(37.=(4?.O2.))(2>.(35.(22.$23.$23.)(25.$23.$23.(50.O2.)(4?.O2.))O4.)(2>.(38.Vsegs,O5.(50.O2.)(0.$1.(;.(39.(4?.O2.))(5?.O1.))(1=.$1.)))(2>.(44.O5.O4.(3<.O3.+40.)(52.O2.)(53.O1.))(2>.(2?.Vsegs,L,(30.$1.)$31.O5.O4.(57.O2.)(5:.O2.))(2>.(60.O5.O4.(58.O2.)(5<.O2.))(3=.$23.(24.(22.$23.$23.)$23.(3>.$23.$23.)(61.O2.))))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition pkcs7_at (st : option (p7_own * p7_junk)) (m : mem) (LBn LB : list blk) (A : Z) : Prop :=
  match st with
  | None => pkcs7_zero m A /\ A mod 8 = 0 /\ 0 < A /\ A + PKCS7_SIZE <= 2 ^ 64   (* [comment removed for export] *)
  | Some (po, j) => pkcs7_live m (LBn ++ LB) A po j /\ List.NoDup LBn /\ (forall b, In b LBn <-> In b (p7_blocks po))
  end.

End WithSegs.
