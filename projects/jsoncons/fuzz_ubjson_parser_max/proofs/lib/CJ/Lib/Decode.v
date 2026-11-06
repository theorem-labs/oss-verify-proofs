(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import PropExec MState Mem ITree Nodes.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Export RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Lib_Decode () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Fork."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Decode."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Decode.CEIL_DEC."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.ITree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Nodes."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.RunP."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1Some"; "1bool"; "1list"; "1option"; "1pair"; "1prod"; "1true"; "2and"; "2eq"; "2or"; "3Forall"; "4Z"; "5errno_ret"; "5page_size"; "5region_free"]; ["6PID_MAX_ENVELOPE"; "0RUNp"; "8mmap_addr_ok"; "7SErr"; "7SVal"; "7avoids"; "7covered"; "7dec_brk0"; "7dec_count"; "7dec_plain"; "7dec_set_tid"; "7errno_of"; "7mmap_len"; "7sret"; "9resp"; ":eff0"]; [":efferr"; ";alloc_ceiling"; "<In"; "=add"; "=le"; "=lt"; "=modulo"; "=pow"; "=sub"; "0a"; "0avoid"; "0b"; "0count"; "0e"; "0hi"; "0len"]; ["0lo"; "0maps"; "0n"; "0ok"; "0r"; "0rsp"; ">Z_to_bv"; ">bv"; ">bv_unsigned"; "0sz"; "0t"; "0x"; "0z"]]).
Ltac kill_eff_tail H :=
exfalso;
repeat match type of H with
| context [match ?x with _ => _ end] => destruct x
end;
discriminate.
Definition errno_of (r : word) : option Z :=
if (2^64 - 4095 <=? bv_unsigned r)%Z then Some (2^64 - bv_unsigned r)%Z else None.
Lemma errno_of_Some : ltac2:(TCodec.tc2 tcn__CJ_Lib_Decode "M'QGyR0%211'<'9'4%113&Kr2%211(1r1%2291%93741'8r3&=%119%>3@31&Q4+1%221=+SoO%42?1%:231%;271p0=1pRLH1pS:J1").
Proof.
intros r e H. unfold errno_of in H. pose proof (bv_unsigned_in_range 64 r) as R. unfold bv_modulus in R.
destruct (Z.leb_spec0 (2^64 - 4095) (bv_unsigned r)); [|discriminate]. inversion H; subst.
split; [|lia]. apply bv_eq. unfold errno_ret. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64)%Z with (2^64)%Z.
replace (- (2 ^ 64 - bv_unsigned r))%Z with (bv_unsigned r + (-1) * 2^64)%Z by lia.
rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma errno_of_errno_ret : ltac2:(TCodec.tc2 tcn__CJ_Lib_Decode "F'<'8&Q4+1r1%3221+SoO%5231%7231'9'4%11;&K&=r2%211%411(1%12B4%:3831p0<1pRLE1").
Proof.
intros e He. unfold errno_of. rewrite errno_ret_unsigned by lia. unfold two_pow_64.
destruct (Z.leb_spec0 (2^64 - 4095) (2^64 - e)); [|lia]. f_equal. lia.
Qed.
Lemma errno_of_small : ltac2:(TCodec.tc2 tcn__CJ_Lib_Decode "K'QGyR0%211&Q4&QHr1%2251&Q8&Q7+2+R0%3221+TP0%6221%;281'9'4'<%211&Kr2%211(0%116%93631p0;1pS:H1").
Proof. intros r H. unfold errno_of. destruct (Z.leb_spec0 (2^64 - 4095) (bv_unsigned r)); [lia|reflexivity]. Qed.
Lemma errno_of_lit : ltac2:(TCodec.tc2 tcn__CJ_Lib_Decode "M'<'8&Q4zr1%3221&Q8&Q7+2+R0%3221+TP0%6221%;291%=291'9'4%11A&K&QFyR0r2%3221%511(0%11I%;3931p0=1pSJL1").
Proof. intros. apply errno_of_small. rewrite unsigned_lit by lia. lia. Qed.
Inductive sret : Type := SErr (e : Z) | SVal (v : Z).
Definition dec_plain (ok : Z -> bool) (rsp : resp) : option sret :=
match rsp with
| mkEffectU r [] [] [] [] [] =>
match errno_of r with
| Some e => Some (SErr e)
| None => if ok (bv_unsigned r) then Some (SVal (bv_unsigned r)) else None
end
| _ => None
end.
Lemma dec_plain_Some : forall ok rsp a, dec_plain ok rsp = Some a ->
match a with
| SErr e => rsp = efferr e /\ (1 <= e <= 4095)%Z
| SVal v => rsp = eff0 (Z_to_bv 64 v) /\ ok v = true /\ (0 <= v <= 2^64 - 4096)%Z
end.
Proof.
intros ok [r ws zs us cs ci] a H. unfold dec_plain in H. destruct cs; [|kill_eff_tail H]. destruct ci; [|kill_eff_tail H]. cbv beta iota in H.
destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
destruct (errno_of r) as [e|] eqn:E.
- inversion H; subst. apply errno_of_Some in E as [-> He]. split; [reflexivity|exact He].
- destruct (ok (bv_unsigned r)) eqn:Hok; [|discriminate]. inversion H; subst.
pose proof (bv_unsigned_in_range 64 r) as R. unfold bv_modulus in R.
unfold errno_of in E. destruct (Z.leb_spec0 (2^64 - 4095) (bv_unsigned r)); [discriminate|].
unfold eff0. rewrite Z_to_bv_bv_unsigned. repeat split; try reflexivity; try exact Hok; lia.
Qed.
Lemma dec_plain_err : ltac2:(TCodec.tc2 tcn__CJ_Lib_Decode "M'<'2p021'8&Q4+1r1%3221+SoO%5231%7231'9'4'M%211&Ir3&Q0r2%211%5241(1(C%115%32;1%>3;51p0@1pRLK1pS8J1").
Proof. intros ok e He. unfold dec_plain, efferr, eff0. rewrite errno_of_errno_ret by lia. reflexivity. Qed.
Lemma dec_plain_val : ltac2:(TCodec.tc2 tcn__CJ_Lib_Decode "Q;'<'2pSH21'8&Q4zr1%3221&Q8&Q7+2+R0%3221+TP0%6221%;291%=291'9r3r2%211(7%53E21'4'M%211&Ir4&O&QFyR0%221=%411%7261(1(D%11B%32=1%E3=51p0A1p0H1pSJQ91pS8Q81").
Proof.
intros ok z Hz Hok. unfold dec_plain, eff0. rewrite errno_of_lit by lia.
rewrite unsigned_lit by lia. rewrite Hok. reflexivity.
Qed.
Inductive read_ans : Type := RdErr (e : Z) | RdData (bs : list byte).
Definition dec_read (buf count : Z) (rsp : resp) : option read_ans :=
match rsp with
| mkEffectU r [] [] [] [] [] =>
match errno_of r with
| Some e => Some (RdErr e)
| None => if (bv_unsigned r =? 0)%Z then Some (RdData []) else None
end
| mkEffectU r [(a, bs)] [] [] [] [] =>
if bv_eqb a (Z_to_bv 64 buf) && (1 <=? Z.of_nat (length bs))%Z
&& (Z.of_nat (length bs) <=? count)%Z && (bv_unsigned r =? Z.of_nat (length bs))%Z
then Some (RdData bs) else None
| _ => None
end.
Section SE.
Local Abbreviation SEC_T_dec_read_Some := (forall buf count rsp a, (0 <= count)%Z -> dec_read buf count rsp = Some a ->
match a with
| RdErr e => rsp = efferr e /\ (1 <= e <= 4095)%Z
| RdData bs => rsp = mkEffect (Z_to_bv 64 (Z.of_nat (length bs))) (delivered_writes (Z_to_bv 64 buf) bs) []
/\ (Z.of_nat (length bs) <= count)%Z
end) (only parsing).
Variable buf : ltac:(sec_ty2 constr:(SEC_T_dec_read_Some) 0%nat 0%nat).
Variable count : ltac:(sec_ty2 constr:(SEC_T_dec_read_Some) 1%nat 0%nat).
Lemma dec_read_Some : ltac:(sec_stmt2 constr:(SEC_T_dec_read_Some) 2%nat 0%nat).
Proof.
intros [r ws zs us cs ci] a Hc H.
unfold dec_read in H. destruct cs; [|kill_eff_tail H]. destruct ci; [|kill_eff_tail H]. cbv beta iota in H.
destruct ws as [|[a0 bs] [|? ?]]; try discriminate.
- destruct zs; [|discriminate]. destruct us; [|discriminate].
destruct (errno_of r) as [e|] eqn:E.
+ inversion H; subst. apply errno_of_Some in E as [-> He]. split; [reflexivity|exact He].
+ destruct (Z.eqb_spec (bv_unsigned r) 0); [|discriminate]. inversion H; subst. cbn.
split; [|lia]. f_equal. apply bv_eq. rewrite unsigned_lit by lia. assumption.
- destruct zs; [|discriminate]. destruct us; [|discriminate].
destruct (bv_eqb a0 (Z_to_bv 64 buf)) eqn:E1; [|discriminate].
destruct (Z.leb_spec0 1 (Z.of_nat (length bs))); [|discriminate].
destruct (Z.leb_spec0 (Z.of_nat (length bs)) count); [|discriminate].
destruct (Z.eqb_spec (bv_unsigned r) (Z.of_nat (length bs))); [|discriminate].
cbn [andb] in H. inversion H; subst. apply bv_eqb_eq in E1. subst a0.
destruct bs as [|b bs']; [cbn in *; lia|]. cbn [delivered_writes]. split; [|lia].
f_equal. apply bv_eq. rewrite unsigned_lit. { assumption. }
pose proof (bv_unsigned_in_range 64 r). unfold bv_modulus in *. lia.
Qed.
End SE.
Definition dec_count (count : Z) (rsp : resp) : option Z :=
match rsp with
| mkEffectU r [] [] [] [] [] => if (bv_unsigned r =? count)%Z then Some count else None
| _ => None
end.
Definition dec_write := dec_count.
Definition dec_writev := dec_count.
Lemma dec_count_Some : ltac2:(TCodec.tc2 tcn__CJ_Lib_Decode "Q6'<&N'9'4%114&Hr3r2%3221(1r1%22;1%:3841'8r4%=3?81&O&QFyR0%2215%411%C3D?1&Q4z%221:&Q5&Q7+2+R0%3221%52@1%B271%C2;1%D2B1p0F1pRDQ31pS<Q31pRJQ51").
Proof.
intros count [r ws zs us cs ci] a H. unfold dec_count in H. destruct cs; [|kill_eff_tail H]. destruct ci; [|kill_eff_tail H]. cbv beta iota in H.
destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
destruct (Z.eqb_spec (bv_unsigned r) count); [|discriminate]. inversion H; subst.
pose proof (bv_unsigned_in_range 64 r) as R. unfold bv_modulus in R.
split; [reflexivity|]. split; [|lia]. unfold eff0. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.
Definition dec_open : resp -> option sret := dec_plain (fun v => (3 <=? v)%Z && (v <=? 4096)%Z).
Definition dec_close : resp -> option sret := dec_plain (fun v => (v =? 0)%Z).
Definition dec_ioctl : resp -> option sret := dec_plain (fun _ => false).
Definition dec_set_tid (rsp : resp) : option Z :=
match rsp with
| mkEffectU r [] [] [] [] [] =>
if (0 <? bv_unsigned r)%Z && (bv_unsigned r <? PID_MAX_ENVELOPE)%Z then Some (bv_unsigned r) else None
| _ => None
end.
Definition dec_exit (rsp : resp) : option Empty_set := None.
Lemma dec_set_tid_Some : ltac2:(TCodec.tc2 tcn__CJ_Lib_Decode "N&N'<'9'4%113&Jr2%211(1r1%2291%93741'8r3&O&QFyR0%221;%411%A3C61&Q5z%221@&@%42B1%=231%>271p0@1pSFK1pS<M1").
Proof.
intros [r ws zs us cs ci] t H. unfold dec_set_tid in H. destruct cs; [|kill_eff_tail H]. destruct ci; [|kill_eff_tail H]. cbv beta iota in H.
destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
destruct (Z.ltb_spec0 0 (bv_unsigned r)); [|discriminate].
destruct (Z.ltb_spec0 (bv_unsigned r) PID_MAX_ENVELOPE); [|discriminate]. inversion H; subst.
unfold eff0. rewrite Z_to_bv_bv_unsigned. split; [reflexivity|lia].
Qed.
Definition dec_brk0 (rsp : resp) : option Z :=
match rsp with mkEffectU r [] [] [] [] [] => Some (bv_unsigned r) | _ => None end.
Lemma dec_brk0_Some : ltac2:(TCodec.tc2 tcn__CJ_Lib_Decode "Q2&N'<'9'4%113&Gr2%211(1r1%2291%93741'8r3&O&QFyR0%221;%411%A3C61&Q4z%221@&Q5&Q7+2+R0%3221%52F1%A271%B2;1p0D1pRHO1pS<Q11").
Proof.
intros [r ws zs us cs ci] b H. unfold dec_brk0 in H. destruct cs; [|kill_eff_tail H]. destruct ci; [|kill_eff_tail H]. cbv beta iota in H.
destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. inversion H; subst.
pose proof (bv_unsigned_in_range 64 r) as R. unfold bv_modulus in R.
unfold eff0. rewrite Z_to_bv_bv_unsigned. split; [reflexivity|lia].
Qed.
Definition brk_new_pages (cur req : Z) : option (Z * Z) :=
let lo := page_round_up_Z cur in let hi := page_round_up_Z req in
if (lo <? hi)%Z then Some (lo, hi - lo)%Z else None.
Definition zeros_of (p : option (Z * Z)) : list (word * word) :=
match p with Some (lo, n) => [(wa lo, Z_to_bv 64 n)] | None => [] end.
Inductive brk_ans : Type := BrkGrown | BrkSame.
Definition dec_brk (cur req : Z) (rsp : resp) : option brk_ans :=
match rsp with
| mkEffectU r [] zs [] [] [] =>
if (bv_unsigned r =? cur)%Z && match zs with [] => true | _ => false end then Some BrkSame
else if (bv_unsigned r =? req)%Z && listNN_eqb zs (zeros_of (brk_new_pages cur req)) then Some BrkGrown
else None
| _ => None
end.
Section SE.
Local Abbreviation SEC_T_dec_brk_Some := (forall cur req rsp a, dec_brk cur req rsp = Some a ->
match a with
| BrkSame => rsp = eff0 (Z_to_bv 64 cur)
| BrkGrown => rsp = mkEffect (Z_to_bv 64 req) [] (zeros_of (brk_new_pages cur req))
end) (only parsing).
Variable cur : ltac:(sec_ty2 constr:(SEC_T_dec_brk_Some) 0%nat 0%nat).
Variable req : ltac:(sec_ty2 constr:(SEC_T_dec_brk_Some) 1%nat 0%nat).
Lemma dec_brk_Some : ltac:(sec_stmt2 constr:(SEC_T_dec_brk_Some) 2%nat 0%nat).
Proof.
intros [r ws zs us cs ci] a H.
unfold dec_brk in H. destruct cs; [|kill_eff_tail H]. destruct ci; [|kill_eff_tail H]. cbv beta iota in H.
destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate].
destruct (Z.eqb_spec (bv_unsigned r) cur).
- destruct zs.
+ cbn [andb] in H. inversion H; subst. unfold eff0. rewrite Z_to_bv_bv_unsigned. reflexivity.
+ cbn [andb] in H. destruct (Z.eqb_spec (bv_unsigned r) req); [|discriminate].
destruct (listNN_eqb _ _) eqn:E; [|discriminate]. inversion H; subst. apply listNN_eqb_eq in E.
rewrite <- E, Z_to_bv_bv_unsigned. reflexivity.
- cbn [andb] in H. destruct (Z.eqb_spec (bv_unsigned r) req); [|discriminate].
destruct (listNN_eqb _ _) eqn:E; [|discriminate]. inversion H; subst. apply listNN_eqb_eq in E.
rewrite <- E, Z_to_bv_bv_unsigned. reflexivity.
Qed.
End SE.
Inductive mmap_ans : Type := MmErr (e : Z) | MmOk (a : Z).
Definition avoids (a n : Z) (avoid : list (Z * Z)) : bool :=
forallb (fun iv => (a + n <=? fst iv)%Z || (snd iv <=? a)%Z) avoid.
Definition mmap_len (len : Z) : Z := page_round_up_Z len.
Section CEIL_DEC.
Context {RUNp : RunP}.
Definition mmap_addr_ok (len : Z) (avoid : list (Z * Z)) (a : Z) : bool :=
(a mod page_size =? 0)%Z && (0 <? a)%Z && (a + mmap_len len <=? alloc_ceiling)%Z && avoids a (mmap_len len) avoid.
Definition dec_mmap (len : Z) (avoid : list (Z * Z)) (rsp : resp) : option mmap_ans :=
match rsp with
| mkEffectU r [] [] [] [] [] => match errno_of r with Some e => Some (MmErr e) | None => None end
| mkEffectU r [] [(a, n)] [] [] [] =>
if bv_eqb a r && bv_eqb n (Z_to_bv 64 (mmap_len len)) && mmap_addr_ok len avoid (bv_unsigned r)
then Some (MmOk (bv_unsigned r)) else None
| _ => None
end.
Definition dec_mmap_none (len : Z) (avoid : list (Z * Z)) (rsp : resp) : option mmap_ans :=
match rsp with
| mkEffectU r [] [] [] [] [] => match errno_of r with Some e => Some (MmErr e) | None => None end
| mkEffectU r [] [] [(a, n)] [] [] =>
if bv_eqb a r && bv_eqb n (Z_to_bv 64 (mmap_len len)) && mmap_addr_ok len avoid (bv_unsigned r)
then Some (MmOk (bv_unsigned r)) else None
| _ => None
end.
Lemma avoids_In : ltac2:(TCodec.tc2 tcn__CJ_Lib_Decode "Q3'<'3'6%1233%311'9'2&Er5r4r3%43321(7%83721&Q2(5r2%24AA71%43?19':&Q4&Q3r7r6%3221%521@%62@4%8221p0:1p0@1pRNN1pS2O1pRFL1pS6Q11pRDQ21").
Proof.
intros a n avoid lo hi H Hin. unfold avoids in H. rewrite forallb_forall in H.
specialize (H _ Hin). cbn in H. apply orb_prop in H as [H|H]; [left|right]; apply Z.leb_le; exact H.
Qed.
Lemma mmap_addr_ok_true : ltac2:(TCodec.tc2 tcn__CJ_Lib_Decode "Q:'<'3'6%1233%311'9'2&Br3r2r1%43321(7%83721'8&Q6&>%2281z%>3C21&Q5%123<&Q4&Q3&Lr4%211%42B1&Q1vA%211%9241%B2;1%C2>1&E%13J9K%O3N1H%G241p0I1pRDQ71pRFQ41pS0Q91").
Proof.
intros len avoid a H. unfold mmap_addr_ok in H.
apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Z.eqb_eq in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. auto.
Qed.
Section SE.
Local Abbreviation SEC_T_dec_mmap_Some := (forall len avoid rsp x, dec_mmap len avoid rsp = Some x ->
match x with
| MmErr e => rsp = efferr e /\ (1 <= e <= 4095)%Z
| MmOk a => rsp = mkEffect (Z_to_bv 64 a) [] [(wa a, Z_to_bv 64 (mmap_len len))] /\ mmap_addr_ok len avoid a = true
end) (only parsing).
Variable len : ltac:(sec_ty2 constr:(SEC_T_dec_mmap_Some) 0%nat 0%nat).
Variable avoid : ltac:(sec_ty2 constr:(SEC_T_dec_mmap_Some) 1%nat 0%nat).
Lemma dec_mmap_Some : ltac:(sec_stmt2 constr:(SEC_T_dec_mmap_Some) 2%nat 0%nat).
Proof.
intros [r ws zs us cs ci] x H.
unfold dec_mmap in H. destruct cs; [|kill_eff_tail H]. destruct ci; [|kill_eff_tail H]. cbv beta iota in H.
destruct ws; [|discriminate]. destruct zs as [|[a n] [|? ?]]; try discriminate.
- destruct us; [|discriminate]. destruct (errno_of r) eqn:E; [|discriminate]. inversion H; subst.
apply errno_of_Some in E as [-> He]. auto.
- destruct us; [|discriminate].
destruct (bv_eqb a r) eqn:E1; [|discriminate]. destruct (bv_eqb n _) eqn:E2; [|discriminate].
destruct (mmap_addr_ok len avoid (bv_unsigned r)) eqn:E3; [|discriminate]. cbn [andb] in H. inversion H; subst.
apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst. unfold wa. rewrite Z_to_bv_bv_unsigned. auto.
Qed.
End SE.
Lemma dec_mmap_none_Some : forall len avoid rsp x, dec_mmap_none len avoid rsp = Some x ->
match x with
| MmErr e => rsp = efferr e /\ (1 <= e <= 4095)%Z
| MmOk a => rsp = mkEffectU (Z_to_bv 64 a) [] [] [(wa a, Z_to_bv 64 (mmap_len len))] [] [] /\ mmap_addr_ok len avoid a = true
end.
Proof.
intros len avoid [r ws zs us cs ci] x H. unfold dec_mmap_none in H. destruct cs; [|kill_eff_tail H]. destruct ci; [|kill_eff_tail H]. cbv beta iota in H.
destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us as [|[a n] [|? ?]]; try discriminate.
- destruct (errno_of r) eqn:E; [|discriminate]. inversion H; subst. apply errno_of_Some in E as [-> He]. auto.
- destruct (bv_eqb a r) eqn:E1; [|discriminate]. destruct (bv_eqb n _) eqn:E2; [|discriminate].
destruct (mmap_addr_ok len avoid (bv_unsigned r)) eqn:E3; [|discriminate]. cbn [andb] in H. inversion H; subst.
apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst. unfold wa. rewrite Z_to_bv_bv_unsigned. auto.
Qed.
End CEIL_DEC.
Inductive range_ans : Type := RgErr (e : Z) | RgDone (changed : bool).
Definition dec_munmap (addr len : Z) (rsp : resp) : option range_ans :=
match rsp with
| mkEffectU r [] [] [] [] [] =>
match errno_of r with Some e => Some (RgErr e) | None => if (bv_unsigned r =? 0)%Z then Some (RgDone false) else None end
| mkEffectU r [] [] [(a, n)] [] [] =>
if (bv_unsigned r =? 0)%Z && bv_eqb a (Z_to_bv 64 addr) && bv_eqb n (Z_to_bv 64 (mmap_len len))
then Some (RgDone true) else None
| _ => None
end.
Definition dec_mprotect (addr len : Z) (rsp : resp) : option range_ans :=
match rsp with
| mkEffectU r [] [] [] [] [] =>
match errno_of r with Some e => Some (RgErr e) | None => if (bv_unsigned r =? 0)%Z then Some (RgDone false) else None end
| mkEffectU r [] [(a, n)] [] [] [] =>
if (bv_unsigned r =? 0)%Z && bv_eqb a (Z_to_bv 64 addr) && bv_eqb n (Z_to_bv 64 (mmap_len len))
then Some (RgDone true) else None
| _ => None
end.
Section SE.
Local Abbreviation SEC_T_dec_munmap_Some := (forall addr len rsp x, dec_munmap addr len rsp = Some x ->
match x with
| RgErr e => rsp = efferr e /\ (1 <= e <= 4095)%Z
| RgDone false => rsp = eff0 (Z_to_bv 64 0)
| RgDone true => rsp = mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 addr, Z_to_bv 64 (mmap_len len))] [] []
end) (only parsing).
Variable addr : ltac:(sec_ty2 constr:(SEC_T_dec_munmap_Some) 0%nat 0%nat).
Variable len : ltac:(sec_ty2 constr:(SEC_T_dec_munmap_Some) 1%nat 0%nat).
Lemma dec_munmap_Some : ltac:(sec_stmt2 constr:(SEC_T_dec_munmap_Some) 2%nat 0%nat).
Proof.
intros [r ws zs us cs ci] x H.
unfold dec_munmap in H. destruct cs; [|kill_eff_tail H]. destruct ci; [|kill_eff_tail H]. cbv beta iota in H.
destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us as [|[a n] [|? ?]]; try discriminate.
- destruct (errno_of r) eqn:E. { inversion H; subst. apply errno_of_Some in E as [-> He]. auto. }
destruct (Z.eqb_spec (bv_unsigned r) 0); [|discriminate]. inversion H; subst.
unfold eff0. f_equal. apply bv_eq. rewrite unsigned_lit by lia. assumption.
- destruct (Z.eqb_spec (bv_unsigned r) 0); [|discriminate].
destruct (bv_eqb a _) eqn:E1; [|discriminate]. destruct (bv_eqb n _) eqn:E2; [|discriminate].
cbn [andb] in H. inversion H; subst. apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst.
f_equal. apply bv_eq. rewrite unsigned_lit by lia. assumption.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_dec_mprotect_Some := (forall addr len rsp x, dec_mprotect addr len rsp = Some x ->
match x with
| RgErr e => rsp = efferr e /\ (1 <= e <= 4095)%Z
| RgDone false => rsp = eff0 (Z_to_bv 64 0)
| RgDone true => rsp = mkEffect (Z_to_bv 64 0) [] [(Z_to_bv 64 addr, Z_to_bv 64 (mmap_len len))]
end) (only parsing).
Variable addr : ltac:(sec_ty2 constr:(SEC_T_dec_mprotect_Some) 0%nat 0%nat).
Variable len : ltac:(sec_ty2 constr:(SEC_T_dec_mprotect_Some) 1%nat 0%nat).
Lemma dec_mprotect_Some : ltac:(sec_stmt2 constr:(SEC_T_dec_mprotect_Some) 2%nat 0%nat).
Proof.
intros [r ws zs us cs ci] x H.
unfold dec_mprotect in H. destruct cs; [|kill_eff_tail H]. destruct ci; [|kill_eff_tail H]. cbv beta iota in H.
destruct ws; [|discriminate]. destruct zs as [|[a n] [|? ?]]; try discriminate.
- destruct us; [|discriminate].
destruct (errno_of r) eqn:E. { inversion H; subst. apply errno_of_Some in E as [-> He]. auto. }
destruct (Z.eqb_spec (bv_unsigned r) 0); [|discriminate]. inversion H; subst.
unfold eff0. f_equal. apply bv_eq. rewrite unsigned_lit by lia. assumption.
- destruct us; [|discriminate]. destruct (Z.eqb_spec (bv_unsigned r) 0); [|discriminate].
destruct (bv_eqb a _) eqn:E1; [|discriminate]. destruct (bv_eqb n _) eqn:E2; [|discriminate].
cbn [andb] in H. inversion H; subst. apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst.
f_equal. apply bv_eq. rewrite unsigned_lit by lia. assumption.
Qed.
End SE.
Definition covered (maps : list (word * word)) (iv : Z * Z) : Prop :=
exists e sz, In (e, sz) maps /\ (bv_unsigned e <= fst iv)%Z /\ (snd iv <= bv_unsigned e + bv_unsigned sz)%Z.
Lemma region_free_In : ltac2:(TCodec.tc2 tcn__CJ_Lib_Decode "Q:'3'6'QGyR0%211%4211%611'9'2&?r5r4r3%43321(7%83721&Q2(5r2%24??71r6%53@21':&Q4&Q3&QH%12G6%22HA%4221%42JB%7221%62LC%8231%:217%<241p0>1p0E1pSDQ11pRLQ21pS6Q31pRDQ41pS4Q31").
Proof.
induction maps as [|[e0 sz0] maps IH]; intros a n e sz H Hin; [destruct Hin|].
cbn [region_free] in H. apply andb_prop in H as [H1 H2].
destruct Hin as [E|Hin]; [|exact (IH _ _ _ _ H2 Hin)].
inversion E; subst. unfold iv_overlap in H1.
destruct (Z.ltb_spec0 (bv_unsigned a) (bv_unsigned e + bv_unsigned sz));
destruct (Z.ltb_spec0 (bv_unsigned e) (bv_unsigned a + bv_unsigned n)); cbn in H1; try discriminate; lia.
Qed.
Lemma avoids_of_region_free : ltac2:(TCodec.tc2 tcn__CJ_Lib_Decode "Q4'3'6'QGyR0%211%4211%611'<%7211%911'9'2&?r4r3r2%43321(7%83721';&Fr5%211%43?18&E&QH%12G5%22H>%4321>%C3B1<p071p0=1pRFG1pS6M1pRDN1pS4M1").
Proof.
intros maps a n avoid Hrf Hc. unfold avoids. apply forallb_forall. intros [lo hi] Hin.
pose proof (proj1 (Forall_forall _ _) Hc _ Hin) as (e & sz & He & H1 & H2). cbn in H1, H2. cbn [fst snd].
pose proof (region_free_In _ _ _ _ _ Hrf He) as [H|H].
- apply orb_true_intro. left. apply Z.leb_le. lia.
- apply orb_true_intro. right. apply Z.leb_le. lia.
Qed.
Lemma mmap_len_bound : ltac2:(TCodec.tc2 tcn__CJ_Lib_Decode "B'<&Q5zr1%3221'8&Q4r2&L%112%4231&Q3+TP0%2261%=251%:251p0<1pS0A1").
Proof. intros len H. unfold mmap_len, page_round_up_Z, page_size. split; [|]; nia || lia. Qed.
