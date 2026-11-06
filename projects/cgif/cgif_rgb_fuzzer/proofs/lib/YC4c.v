(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YF8z YC1d YC1a YC2o YC10 YC2p YC1b YC46.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require YR00.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition boxed (P : Prop) : Prop := P.
Ltac box H := lazymatch type of H with ?T => change T with (boxed T) in H end.
Ltac unbox := unfold boxed in *.
Ltac rwEFA := repeat match goal with H : forall c p, frame_addr ?l3 c p = frame_addr ?l c p |- context [frame_addr ?l3 _ _] =>
tryif constr_eq l3 l then fail else rewrite !H end.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition ss_set_pc (s : sstate) (pc : Z) : sstate := mkSS pc (ss_regs s) (ss_mem s) (ss_resv s) (ss_facts s).
Fixpoint list_set {A} (l : list A) (i : nat) (x : A) : list A :=
match l, i with [], _ => [] | _ :: t, O => x :: t | h :: t, S j => h :: list_set t j x end.
Definition ss_set_reg (s : sstate) (r : nat) (e : sv) : sstate := mkSS (ss_pc s) (list_set (ss_regs s) r e) (ss_mem s) (ss_resv s) (ss_facts s).
Fixpoint ss_set_regs (s : sstate) (l : list (nat * sv)) : sstate :=
match l with [] => s | (r, e) :: t => ss_set_regs (ss_set_reg s r e) t end.
Fixpoint ss_havoc_regs (s : sstate) (N : nat) (deads : list nat) : sstate :=
match deads with [] => s | r :: t => ss_havoc_regs (ss_set_reg s r (SOff N 0)) (S N) t end.
Fixpoint facts_set (fa : list (nat * afact)) (n : nat) (af : afact) : list (nat * afact) :=
match fa with [] => [] | (m, a) :: t => if Nat.eqb m n then (m, af) :: t else (m, a) :: facts_set t n af end.
Definition ss_set_fact (s : sstate) (n : nat) (af : afact) : sstate :=
mkSS (ss_pc s) (ss_regs s) (ss_mem s) (ss_resv s) (mkFacts (facts_set (f_atoms (ss_facts s)) n af) (f_conds (ss_facts s)) (f_alias (ss_facts s))).
Definition ss_set_mem (s : sstate) (m : smem) : sstate := mkSS (ss_pc s) (ss_regs s) m (ss_resv s) (ss_facts s).
Definition ss_set_facts (s : sstate) (fa : list (nat * afact)) : sstate :=
mkSS (ss_pc s) (ss_regs s) (ss_mem s) (ss_resv s) (mkFacts fa (f_conds (ss_facts s)) (f_alias (ss_facts s))).
Definition ss_A2 : sstate :=
ltac2:(YR00.build ['(mkSST); '(@cons sv); '(SLit); '(SOff); '(SAlu); '(ALU_ADD); '(ALU_SRL); '(SExt); '(true); '(@nil sv); '(@cons YQ0b.region); '(YQ0b.mkRegion); '(@Some nat); '(@cons YQ0b.chunk); '(YQ0b.mkChunk); '(CVal); '(@nil YQ0b.chunk); '(@None nat); '(@nil YQ0b.region); '(@None sv); '(mkFacts); '(@cons (prod nat afact)); '(@pair nat afact); '(mkAF); '(@nil (prod nat afact)); '(@nil acond); '(@cons (prod sv sv)); '(@pair sv sv); '(@nil (prod sv sv))] [24;2240545;40;68;1;40;104;214;1;40;104;10;3;320;40;104;14;1;40;104;18;1;40;104;218;1;40;104;222;1;40;104;226;1;40;104;10;1;40;104;10;3;320;40;104;46;121;40;68;25;40;104;302;1;40;140;160;140;192;104;46;121;68;13;104;162;1;40;104;46;65;40;140;160;140;192;104;46;65;68;13;104;162;1;40;68;7;1;3;1073741811;1073741823;15;40;104;258;1;40;104;230;1;40;104;174;1;40;104;282;1;40;236;256;15;32;104;158;1;40;140;160;140;192;104;42;161;68;13;104;162;1;40;104;198;1;40;104;46;1;40;104;42;161;40;104;230;1;40;104;42;1;40;104;262;1;40;104;266;1;40;104;270;1;40;104;274;1;288;288;328;376;388;282;1;65;1;1;424;456;29;488;15;1;68;9;424;456;25;488;15;1;68;1;424;456;21;488;15;1;68;7;1;3;1073741810;1073741823;15;424;456;17;488;15;1;68;7;1;3;1073741816;1073741823;15;424;456;45;488;15;1;68;7;1;3;1073741810;1073741823;15;424;456;41;488;15;1;68;1;424;456;37;488;15;1;68;7;1;3;1073741810;1073741823;15;424;456;33;488;15;1;68;7;1;3;1073741810;1073741823;15;424;456;61;488;15;1;68;7;1;3;1073741811;1073741823;15;424;456;57;488;15;1;68;7;1;3;1073741816;1073741823;15;424;456;53;488;15;1;68;7;1;3;1073741810;1073741823;15;424;456;49;488;15;1;68;7;1;3;1073741810;1073741823;15;424;456;13;488;15;1;68;7;1;3;1073741809;1073741823;15;424;456;9;488;15;1;68;7;1;3;1073741809;1073741823;15;424;456;5;488;15;1;68;7;1;3;1073741809;1073741823;15;424;456;1;488;15;1;68;7;1;3;1073741809;1073741823;15;512;328;376;388;230;1;197;1;197;424;456;65;488;15;8;68;2239041;424;456;33;488;15;8;68;290169;424;456;1;488;15;8;68;4409666253;512;328;376;388;230;197;233;197;233;512;328;376;388;230;233;513;233;513;424;456;481;488;15;8;104;278;1;512;328;376;388;10;3;320;1;3;320;1;424;456;3;136;488;15;8;104;162;1;424;456;3;128;488;15;8;104;230;1;424;456;3;104;488;15;8;104;110;1;424;456;3;96;488;15;8;104;106;1;424;456;3;88;488;15;8;104;102;1;424;456;3;80;488;15;8;104;98;1;424;456;3;72;488;15;8;104;94;1;424;456;3;64;488;15;8;104;90;1;424;456;3;56;488;15;8;104;86;1;424;456;3;48;488;15;8;104;82;1;424;456;3;40;488;15;8;104;78;1;424;456;3;32;488;15;8;104;74;1;424;456;3;24;488;15;8;104;38;1;424;456;3;16;488;15;8;104;34;1;424;456;3;8;488;15;8;104;6;1;424;456;3;320;488;15;8;68;1;512;328;376;544;2655617;2655649;1;1;424;456;2655617;488;15;8;68;2787041;512;328;376;544;2787041;2787073;1;1;424;456;2787041;488;15;8;104;162;1;512;328;376;544;2655969;2656001;1;1;424;456;2655969;488;15;8;68;2787073;512;328;376;544;2787073;2787089;1;1;424;456;2787073;488;15;4;68;5;512;328;376;544;2668449;2668481;1;1;424;456;2668449;488;15;8;68;2239041;512;328;376;388;42;1;193;161;177;424;456;1;488;15;8;68;2191249;424;456;33;488;15;8;104;130;1;424;456;65;488;15;8;104;134;1;424;456;97;488;15;4;104;138;1;424;456;113;488;15;2;104;142;1;424;456;121;488;15;2;104;146;1;424;456;129;488;15;2;104;150;1;424;456;137;488;15;2;104;154;1;424;456;161;488;15;4;104;158;1;512;328;376;388;46;1;161;1;1;424;456;1;488;15;8;104;166;1;424;456;33;488;15;8;104;170;1;424;456;65;488;15;4;104;174;1;424;456;81;488;15;2;104;178;1;424;456;89;488;15;2;104;182;1;424;456;97;488;15;2;104;186;1;424;456;105;488;15;2;104;190;1;424;456;113;488;15;2;104;194;1;424;456;121;488;15;2;104;198;1;424;456;129;488;15;1;104;202;1;424;456;133;488;15;1;104;206;1;512;328;376;388;130;1;385;1;1;424;456;225;488;15;8;68;2119313;424;456;257;488;15;8;104;210;1;424;456;321;488;15;8;68;1;512;576;608;652;680;712;282;748;8589805569;70377333981185;9;680;712;278;748;16385;562949919866881;1;680;712;230;748;16385;562949919866881;21;680;712;10;748;281474976710657;562949953421313;21;680;712;42;748;16385;562949919866881;17;680;712;46;748;16385;562949919866881;13;680;712;130;748;16385;562949919866881;17;680;712;134;748;1;7;1;3;1073741823;1073741823;15;1;680;712;138;748;1;17179869181;1;680;712;142;748;1;262141;1;680;712;146;748;1;262141;1;680;712;150;748;1;1025;1;680;712;154;748;1;262141;1;680;712;158;748;1;17179869181;1;680;712;162;748;8589803521;8589803521;1;680;712;166;748;1;7;1;3;1073741823;1073741823;15;1;680;712;170;748;16385;562949919866881;17;680;712;174;748;1;17179869181;1;680;712;178;748;5;262141;1;680;712;182;748;5;262141;1;680;712;186;748;1;262141;1;680;712;190;748;1;262141;1;680;712;194;748;1;262141;1;680;712;198;748;1;262141;1;680;712;202;748;1;1021;1;680;712;206;748;1;1021;1;680;712;210;748;1;7;1;3;1073741823;1073741823;15;1;768;800;840;872;140;160;140;192;104;230;1;68;13;104;162;1;104;282;1;896]).
Definition ss_B8 : sstate := Eval vm_compute in ss_havoc_regs (ss_set_pc ss_A2 0x88c10) 100 [11; 21]%nat.
Definition ss_C : sstate := Eval vm_compute in
ss_set_fact (ss_set_reg (ss_set_pc ss_B8 0x88c2c) 11 (SLit 257)) 49 (mkAF 0 256 0).
Definition ra_deads_X : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 19; 21; 22; 23; 24; 25; 27; 28; 29; 30; 31]%bv.
Definition ra_saved_chunks : list YQ0b.chunk :=
ltac2:(YR00.build ['(@cons YQ0b.chunk); '(YQ0b.mkChunk); '(CVal); '(SOff); '(@nil YQ0b.chunk)] [8;40;3;104;72;15;8;104;110;1;8;40;3;96;72;15;8;104;106;1;8;40;3;88;72;15;8;104;102;1;8;40;3;80;72;15;8;104;98;1;8;40;3;72;72;15;8;104;94;1;8;40;3;64;72;15;8;104;90;1;8;40;3;56;72;15;8;104;86;1;8;40;3;48;72;15;8;104;82;1;8;40;3;40;72;15;8;104;78;1;8;40;3;32;72;15;8;104;74;1;8;40;3;24;72;15;8;104;38;1;8;40;3;16;72;15;8;104;34;1;8;40;3;8;72;15;8;104;6;1;128]).
Definition ra_raw_ro_chunks : list YQ0b.chunk :=
[YQ0b.mkChunk 0 (CVal 8 (SLit A_cgif_writecb)); YQ0b.mkChunk 8 (CVal 8 (SOff 32 0)); YQ0b.mkChunk 16 (CVal 8 (SOff 33 0));
YQ0b.mkChunk 24 (CVal 4 (SOff 34 0)); YQ0b.mkChunk 28 (CVal 2 (SOff 35 0)); YQ0b.mkChunk 30 (CVal 2 (SOff 36 0));
YQ0b.mkChunk 32 (CVal 2 (SOff 37 0)); YQ0b.mkChunk 34 (CVal 2 (SOff 38 0))].
Definition ra_X_mem : smem :=
[ YQ0b.mkRegion (Some 70%nat) 0 16 0 0 [];
YQ0b.mkRegion (Some 57%nat) 0 49 0 49 [];
YQ0b.mkRegion (Some 57%nat) 58 128 58 128 [YQ0b.mkChunk 120 (CVal 8 (SOff 69 0))];
YQ0b.mkRegion (Some 2%nat) (-104) 0 (-104) 0 ra_saved_chunks;
YQ0b.mkRegion (Some 10%nat) 0 48 40 44 ra_raw_ro_chunks ].
Definition ra_X_atoms : list (nat * afact) :=
[ (70%nat, mkAF 2147451392 17594333495296 2); (69%nat, HPTR 0); (57%nat, HPTR 5);
(2%nat, mkAF (2^46) (2^47) 5); (10%nat, HPTR 4); (11%nat, HPTR 3); (32%nat, HPTR 4); (40%nat, mkAF SB SB 0) ].
Definition ra_X_alias : list (sv * sv) := [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 57 0) (SLit 3)) (SOff 40 0), SOff 70 0)].
Definition ss_X : sstate := Eval vm_compute in
mkSS 0x89434 [SLit 0; SOff 930 0; SOff 2 (-320); SOff 3 0; SOff 4 0; SOff 931 0; SOff 932 0; SOff 933 0; SOff 2 0; SOff 2 (-320); SOff 934 0; SOff 935 0; SOff 936 0; SOff 937 0; SOff 938 0; SOff 939 0; SOff 940 0; SOff 941 0; SOff 57 0; SOff 942 0; SOff 70 0; SOff 943 0; SOff 944 0; SOff 945 0; SOff 946 0; SOff 947 0; SOff 57 0; SOff 948 0; SOff 949 0; SOff 950 0; SOff 951 0; SOff 952 0] ra_X_mem None (mkFacts ra_X_atoms [] ra_X_alias).
Definition ss_X1 : sstate := Eval vm_compute in
mkSS 0x8942c [SLit 0; SOff 900 0; SOff 2 (-320); SOff 3 0; SOff 4 0; SOff 901 0; SOff 902 0; SOff 903 0; SOff 2 0; SOff 2 (-320); SOff 904 0; SOff 905 0; SOff 906 0; SOff 907 0; SOff 908 0; SOff 909 0; SOff 910 0; SOff 911 0; SOff 57 0; SOff 912 0; SOff 70 0; SOff 913 0; SOff 914 0; SOff 915 0; SOff 916 0; SOff 917 0; SOff 57 0; SOff 918 0; SOff 919 0; SOff 920 0; SOff 921 0; SOff 922 0] ra_X_mem None (mkFacts ra_X_atoms [] ra_X_alias).
Record racx := mkRACX {
c_ly : alayout; c_S : astate; c_W : world trasegs; c_regs : bvmap 5 word; c_mem : word -> option byte; c_md : Model;
c_ch : list (Z * Z * Z);
c_raw : Z; c_g : Z; c_cfp : Z; c_gct : Z; c_rattr : Z; c_Wd : Z; c_Hd : Z; c_sgct : Z; c_loops : Z; c_rcur : Z; c_ctx : Z;
c_lct : Z; c_img : Z; c_fattr : Z; c_w : Z; c_h : Z; c_top : Z; c_left : Z; c_delay : Z; c_slct : Z; c_disp : Z; c_tidx : Z;
c_Nimg : Z; c_rest : list (Z * Z); c_cid : Z; c_pos : Z; c_fpos : Z; c_E0 : env }.
Definition ra_vals (cx : racx) : list Z :=
[c_g cx; c_gct cx; c_rattr cx; c_Wd cx; c_Hd cx; c_sgct cx; c_loops cx; c_rcur cx; SB; c_lct cx; c_img cx; c_fattr cx;
c_w cx; c_h cx; c_top cx; c_left cx; c_delay cx; c_slct cx; c_disp cx; c_tidx cx; c_ctx cx].
Definition ra_base (B : asyms) (cx : racx) : Prop :=
afn_pre trasegs B TRAWADD_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) (c_ch cx) /\
spZ (c_regs cx) mod 32 = 0 /\
In (raZ (c_regs cx) :: spine (c_ch cx)) CTX_cgif_raw_addframe /\ Z.of_nat (length (frames (c_S cx))) <= 8 /\
arodata_ok B (aview trasegs (w_H (c_W cx)) (c_mem cx)) /\
getr (c_regs cx) 10 = w64 (c_raw cx) /\ getr (c_regs cx) 11 = w64 (c_cfp cx) /\
(In (c_cid cx, c_pos cx) (frames (c_S cx)) /\ 0 <= c_cid cx /\ frame_addr (c_ly cx) (c_cid cx) (c_pos cx) mod 8 = 0 /\
frame_addr (c_ly cx) (c_cid cx) (c_pos cx) <= c_cfp cx /\ c_cfp cx + 40 <= frame_addr (c_ly cx) (c_cid cx) (c_pos cx) + fs_frame_bytes (c_cid cx) /\
c_cfp cx mod 8 = 0 /\ range_addressable (aview trasegs (w_H (c_W cx)) (c_mem cx)) SHADOW_OFF (c_cfp cx) 40) /\
obj_at trasegs (mrestrict (w_H (c_W cx)) (c_mem cx)) (c_cfp cx) LAY_RawFrameConfig
[c_lct cx; c_img cx; c_fattr cx; c_w cx; c_h cx; c_top cx; c_left cx; c_delay cx; c_slct cx; c_disp cx; c_tidx cx] /\
obj_at trasegs (mrestrict (w_H (c_W cx)) (c_mem cx)) (c_raw cx) LAY_Raw
[A_cgif_writecb; c_g cx; c_gct cx; c_rattr cx; c_Wd cx; c_Hd cx; c_sgct cx; c_loops cx; c_rcur cx] /\
c_sgct cx <= 256 /\
val_mem trasegs (mrestrict (w_H (c_W cx)) (c_mem cx)) (c_g cx + 56) 8 A_writecb /\
val_mem trasegs (mrestrict (w_H (c_W cx)) (c_mem cx)) (c_g cx + 64) 8 (c_ctx cx) /\ 0 <= c_ctx cx < 2 ^ 64 /\
val_mem trasegs (mrestrict (w_H (c_W cx)) (c_mem cx)) (c_g cx + 80) 8 0 /\
1 <= c_w cx /\ 1 <= c_h cx /\ c_w cx * c_h cx <= 100000000 /\ c_w cx * c_h cx <= c_Nimg cx /\
Permutation (ablocks B (c_ly cx) (c_S cx)) ((c_raw cx, RAW_SIZE) :: (c_g cx, CGIF_SIZE) :: (c_img cx, c_Nimg cx) :: c_rest cx) /\
(0 < c_slct cx <= 256 -> exists Nl rest', Permutation (c_rest cx) ((c_lct cx, Nl) :: rest') /\ 3 * c_slct cx <= Nl) /\
vev (c_S cx) + EV_RAWADD <= VEV_MAX /\ blocks_bytes (c_S cx) + LIVE_RAWADD <= LIVE_MAX /\
(forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (c_E0 cx) n = getr (c_regs cx) r) /\
(forall j, (j < 21)%nat -> ew (c_E0 cx) (32 + j) = Z_to_bv 64 (nth j (ra_vals cx) 0)) /\
bv_unsigned (ew (c_E0 cx) 2) = spZ (c_regs cx).
Definition ra_F (cx : racx) : Z := frame_addr (c_ly cx) 1 (c_fpos cx).
Definition ra_FL (cx : racx) : Z := flag_addr (c_ly cx) 1 (c_fpos cx).
Definition ra_E (cx : racx) (E : env) : Prop :=
(forall n, (n < 33)%nat -> ew E n = ew (c_E0 cx) n) /\
(forall j, (1 <= j < 21)%nat -> ew E (32 + j) = Z_to_bv 64 (nth j (ra_vals cx) 0)) /\
ew E 57 = Z_to_bv 64 (ra_F cx) /\ ew E 69 = Z_to_bv 64 (ra_FL cx) /\ ew E 70 = Z_to_bv 64 (SB + ra_F cx / 8).
Definition ra_post (B : asyms) (cx : racx) : world trasegs -> config -> Prop :=
apost_base B TRAWADD_STK [(c_raw cx + 40, c_raw cx + 44)] (c_regs cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) EV_RAWADD
(fun ly' S' W' regs' mem' md' => exists res rcur' : Z,
getr regs' 10 = w64 res /\ 0 <= res < 2 ^ 64 /\
obj_at trasegs (mrestrict (w_H W') mem') (c_raw cx) LAY_Raw
[A_cgif_writecb; c_g cx; c_gct cx; c_rattr cx; c_Wd cx; c_Hd cx; c_sgct cx; c_loops cx; rcur'] /\
Permutation (ablocks B ly' S') (ablocks B (c_ly cx) (c_S cx))).
Definition ra_from (B : asyms) (ss : sstate)
(INV : racx -> env -> Z -> alayout -> astate -> world trasegs -> machine_state -> Model -> Prop) : Prop :=
forall (cx : racx) (E : env) (k : Z) ly3 S3 W3 (ms3 : machine_state) md3,
ra_base B cx -> ra_E cx E ->
ajournal trasegs B TRAWADD_STK (spZ (c_regs cx)) [(c_raw cx + 40, c_raw cx + 44)] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
[(1, c_fpos cx)] ly3 S3 W3 (ms_mem ms3) md3 k ->
frames S3 = (1, c_fpos cx) :: frames (c_S cx) ->
INV cx E k ly3 S3 W3 ms3 md3 ->
st_ok trasegs E ss (restrict (w_H W3) ms3) ->
SRr trasegs W3 (mkCfg ms3 md3) (ra_post B cx).
Definition INV_0 (B : asyms) (kmax : Z) : racx -> env -> Z -> alayout -> astate -> world trasegs -> machine_state -> Model -> Prop :=
fun cx E k ly3 S3 W3 ms3 md3 => k <= kmax /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx).
Definition INV_X (B : asyms) : racx -> env -> Z -> alayout -> astate -> world trasegs -> machine_state -> Model -> Prop :=
fun cx E k ly3 S3 W3 ms3 md3 => k <= EV_RAWADD /\ Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx)).

Lemma ra_E_havoc : forall cx E N vs, (71 <= N)%nat -> ra_E cx E -> ra_E cx (havoc E N vs).
Proof.
intros cx E N vs HN (AG & EX & E57 & E69 & E70). unfold ra_E. rewrite !ew_havoc_old by lia.
split; [|split; [|split; [exact E57 | split; [exact E69 | exact E70]]]].
- intros n Hn. rewrite ew_havoc_old by lia. apply AG. exact Hn.
- intros j Hj. rewrite ew_havoc_old by lia. apply EX. exact Hj.
Qed.


End b.
