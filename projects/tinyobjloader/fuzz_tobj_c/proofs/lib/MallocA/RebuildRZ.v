(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "pow"; "mul"; "sub"; "div"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "or"; "False"; "not"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildRZ"; "envR"; "geoR"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition envR (SB T c nf mu : Z) (z : Z) : Prop := ltac2:(tb__ "0|b|
S9S8S0S1S1VSB;S3Z2M0Z25A2A2S4Vc;Z80M1A2A2M2Vz;A2S2Vz;S1G2G1A2A2A2S9S8S0S1S1VT;Zd0A2S4Z50M3Vc;A2A2M4Vz;A2S2Vz;S1G4Z4M5A2A2A2S9S8S0S1G4Z10A2Vz;A2S2Vz;S1G4G3A2A2A2S9S8S0S1S1S1VSB;S4Vc;S3G0Z20A2M6A2A2M7S5G6S3G0Z1dA2A2A2M8S4G5Vnf;A2A2Vz;A2S2Vz;S1G7G6A2M9A2A2S9S8S0S1G7Vmu;A2MaVz;A2S2Vz;G8A2A2S8S0SdGaA1Vz;A2S2Vz;SdG9A1A2A2A2A2A2A2A2").

Definition geoR (SB T top : Z) : Prop := ltac2:(tb__ "0|4|
S8S0Z10007fff8000M0VSB;A2S8S0S1S1VSB;S3Z2Z25A2A2Z1000M1A2M2Vtop;A2S8S8S0Z7fff7f800000Vtop;A2S0Vtop;Z7fffff800000A2A2S8S0G1VT;A2S8S0S1VT;G1A2M3Vtop;A2S8S9S0G3VSB;A2S0G2VT;A2A2S9S0G3Z7fff7000A2S0G0VT;A2A2A2A2A2A2A2A2").

Lemma Sh_add_le : ltac2:(tb__ "0|1|
S7S7S7S0Z0R3A2M0G0S0S1R5R4A2R3A2S0S1SdR6A1S6R5Z8A2A2SdR4A1A2F_;F_;F_;Fb;Fs;Fa;").
Proof. intros a s b Ha Hs Hab. unfold Sh. lia. Qed.

Lemma Sh_band : ltac2:(tb__ "0|1|
S7S8S0Z0R1A2S0R1S3Z2Z2fA2A2A2S8S0Z7fff8000SdR2A1M0A2S0G0Z10007fff8000A2A2F_;Fa;").
Proof. intros a Ha. unfold Sh, SHADOW_OFF. lia. Qed.

Lemma env_where : ltac2:(tb__ "0|4|
S7S7S7S7S7S7S7SfR7R6R5A3S8S0Z1R5A2S0R5Z1eA2A2S0Z0R5A2M0S8G0S0R5S5S3Z2M1Z20A2M2S3G1Z1dA2A2A2A2SeRbRaR8R7R6R5A6S9S8S0S1RcG2A2R6A2S2R6S1S1RcS3G1Z25A2A2M3Z1000A2A2A2S9S8S0S1RbZ120A2R6A2S2R6S1RbZa80A2A2A2S8S8S0SdRcA1R6A2S2R6SdG3A1A2A2S8S0Z7fff8000R6A2S2R6Z10007fff8000A2A2A2A2A2F_;F_;F_;F_;F_;Fz;Fmu;Fnf;Fc;Ftop;FT;FSB;").
Proof.
  intros SB T top c nf mu z (S1 & S2 & TG & T1 & T2 & ST & TB) Hc Hnf Hmu HE. unfold envR in HE.
  destruct HE as [H|[H|[H|[H|[H|H]]]]].
  - left. lia.
  - right; left. lia.
  - right; left. lia.
  - left. lia.
  - left. lia.
  - right; right.
    pose proof (Sh_mono SB (SB + c * 2 ^ 32 + mu) ltac:(lia)) as M1.
    pose proof (Sh_mono (SB + c * 2 ^ 32 + 2 ^ 32) (SB + 2 ^ 37) ltac:(lia)) as M2.
    pose proof (Sh_band SB ltac:(lia)) as B1. pose proof (Sh_band (SB + 2 ^ 37) ltac:(lia)) as B2.
    lia.
Qed.

Lemma env_out : ltac2:(tb__ "0|3|
S7S7S7S7S7S7S7S7S7SfR9R8R7A3S8S0Z1R7A2S0R7Z1eA2A2S0Z0R7A2M0S8G0S0R7S5S3Z2M1Z20A2M2S3G1Z1dA2A2A2A2S8S0R7R5A2S2R5R6A2A2S9S0R7S1ReG2A2A2S0S1S1ReS3G1Z25A2A2Z1000A2R8A2A2S9S0R8S1ReZ120A2A2S0S1ReZa80A2R9A2A2S9S0R9Z7fff8000A2S0Z10007fff8000RaA2A2SeR11R10ReRdRcR9A6SaF_;F_;F_;F_;F_;F_;F_;F_;F_;Fz;Fhi;Flo;Fmu;Fnf;Fc;Ftop;FT;FSB;").
Proof.
  intros SB T top c nf mu lo hi z HG Hc Hnf Hmu Hz O1 O2 O3 HE.
  destruct (env_where SB T top c nf mu z HG Hc Hnf Hmu HE) as [W|[W|[_ W]]]; lia.
Qed.

Lemma env_sh_out : ltac2:(tb__ "0|4|
S7S7S7S7S7S7S7S7S7SfR9R8R7A3S8S0Z1R7A2S0R7Z1eA2A2S0Z0M0R7A2M1S8G1S0R7S5S3Z2M2Z20A2M3S3G2Z1dA2A2A2A2S8S0SdR7A1R5A2S2R5SdR6A1A2A2S0G0R8A2S0R8S3G2Z2fA2A2S9S0R9S1R10G3A2A2S0S1R10S3G2Z25A2A2RaA2A2SeR11R10ReRdRcR9A6SaF_;F_;F_;F_;F_;F_;F_;F_;F_;Fz;Fhi;Flo;Fmu;Fnf;Fc;Ftop;FT;FSB;").
Proof.
  intros SB T top c nf mu lo hi z HG Hc Hnf Hmu Hz L0 HT OS HE. pose proof HG as (S1 & S2 & TG & T1 & T2 & ST & TB).
  assert (LH : lo <= hi) by (destruct (Z_le_dec lo hi) as [X|X]; [exact X|]; pose proof (Sh_mono hi lo ltac:(lia)); lia).
  pose proof (Sh_band lo ltac:(lia)) as B1. pose proof (Sh_band hi ltac:(lia)) as B2.
  unfold envR in HE. destruct HE as [H|[H|[H|[H|[H|H]]]]]; try lia.
  destruct OS as [O|O].
  - pose proof (Sh_mono hi (SB + c * 2 ^ 32 + mu) ltac:(lia)). lia.
  - pose proof (Sh_mono (SB + c * 2 ^ 32 + 2 ^ 32) lo ltac:(lia)). lia.
Qed.

Lemma slot_out : ltac2:(tb__ "0|7|
S7S7S7S7S7S7S7S7S7S7SfRaR9R8A3S8S0Z1R8A2S0R8Z1eA2A2M0S0Z0R8A2M1S8G1S0R8S5S3Z2M2Z20A2M3S3G2Z1dA2A2M4A2A2G0G1G1S0S1RaR9A2G4A2S9SbScS7RcRfA3A1S0S1RbRaA2RdA2A2S9S8S0S1S1R13S4RdG3A2A2RcA2M5RaA2S2RaS1G5RbA2A2A2S8S0SdG5A1M6RaA2S2RaS1G6S6RbZ8A2A2A2A2A2SeR14R13R11R10RfRbA6SaF_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fz;FS';Fo';Fc';Fmu;Fnf;Fc;Ftop;FT;FSB;").
Proof.
  intros SB T top c nf mu c' o' S' z HG Hc Hnf Hmu Hc' Ho' HS' HE' SEP Hz HE. pose proof HG as (S1 & S2 & TG & T1 & T2 & ST & TB).
  set (ab := SB + c' * 2 ^ 32 + o') in *.
  assert (AB : SB + 2 ^ 32 <= ab /\ ab + S' <= SB + c' * 2 ^ 32 + (2 ^ 32 - 2 ^ 29)) by (unfold ab; lia).
  pose proof (Sh_band ab ltac:(lia)) as B1.
  pose proof (Sh_add_le ab S' (SB + c' * 2 ^ 32 + (2 ^ 32 - 2 ^ 29)) ltac:(lia) HS' ltac:(lia)) as B2.
  pose proof (Sh_band (SB + c' * 2 ^ 32 + (2 ^ 32 - 2 ^ 29)) ltac:(lia)) as B3.
  unfold envR in HE. destruct Hz as [Hz|Hz].
  -
    destruct HE as [H|[H|[H|[H|[H|H]]]]]; try lia.
    pose proof (Sh_band (SB + c * 2 ^ 32 + 2 ^ 32) ltac:(lia)). lia.
  -
    destruct HE as [H|[H|[H|[H|[H|H]]]]]; try lia.
    destruct (Z_lt_dec c' c) as [LT|GE]; [|destruct (Z.eq_dec c' c) as [EQ|NE]].
    + pose proof (Sh_add_le ab S' (SB + c * 2 ^ 32 + mu) ltac:(lia) HS' ltac:(unfold ab; lia)). lia.
    + destruct SEP as [X|X]; [contradiction|]. subst c'.
      pose proof (Sh_add_le ab S' (SB + c * 2 ^ 32 + mu) ltac:(lia) HS' ltac:(unfold ab; lia)). lia.
    + pose proof (Sh_mono (SB + c * 2 ^ 32 + 2 ^ 32) ab ltac:(unfold ab; lia)). lia.
Qed.

Lemma clsfoot_out : ltac2:(tb__ "0|f|
S7S7S7S7S7S7S7S7S7S7SfRaR9R8A3S8S0Z1R8A2S0R8Z1eA2A2M0S0Z0M1R8A2M2S8G2S0R8S5S3Z2M3Z20A2M4S3G3Z1dA2M5A2M6A2A2G0SbScS7R9RcA3A1S8S0G1R9A2M7S0R9G5A2A2S8G7S0R9G6A2A2S9S8S0S1S1R12S3G3Z25A2A2S4RcZ80M8A2A2M9R9A2S2R9S1G9G8A2A2A2S9S8S0S1S1R12S4RcG4A2A2MaG6A2MbR9A2S2R9S1GbRbA2A2A2S9S8S0GaR9A2S2R9S1GaRaA2McA2A2S9S8S0SdGaA1R9A2S2R9SdGcA1A2A2S8S0S1S1R11Zd0A2S4Z50MdRcA2A2MeR9A2S2R9S1GeGdA2A2A2A2A2A2A2SeR13R12R10RfReRaA6SaF_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fz;Fmu';Fmfa';Fc';Fmu;Fnf;Fc;Ftop;FT;FSB;").
Proof.
  intros SB T top c nf mu c' mfa' mu' z HG Hc Hnf Hmu Hc' Hne Hmfa' Hmu' Hz HE. pose proof HG as (S1 & S2 & TG & T1 & T2 & ST & TB).
  pose proof (Sh_band (SB + c' * 2 ^ 32) ltac:(lia)) as B1. pose proof (Sh_band (SB + c' * 2 ^ 32 + mu') ltac:(lia)) as B2.
  pose proof (Sh_band (SB + c * 2 ^ 32 + mu) ltac:(lia)) as B3. pose proof (Sh_band (SB + c * 2 ^ 32 + 2 ^ 32) ltac:(lia)) as B4.
  unfold envR in HE.
  destruct Hz as [Hz|[Hz|[Hz|[Hz|Hz]]]]; destruct HE as [H|[H|[H|[H|[H|H]]]]]; try lia.
  destruct (Z_lt_dec c' c) as [LT|GE].
  - pose proof (Sh_mono (SB + c' * 2 ^ 32 + mu') (SB + c * 2 ^ 32 + mu) ltac:(lia)). lia.
  - pose proof (Sh_mono (SB + c * 2 ^ 32 + 2 ^ 32) (SB + c' * 2 ^ 32) ltac:(lia)). lia.
Qed.

Lemma own_out : ltac2:(tb__ "0|a|
S7S7S7S7S7S7S7SfR7R6R5A3S8S0Z1R5A2S0R5Z1eA2A2S0Z0M0R5A2S0S4Z4M1R6A2S3Z2M2Z1dA2M3A2S8S0G0R6A2S0R6S5S3G2Z20A2M4G3A2M5A2A2S9S8S0S1RcS4R9G4A2A2M6R6A2S2R6S1G6R7A2M7A2A2S9S8S0SdG6A1R6A2S2R6SdG7A1A2A2S9S8S0S1G6G5A2M8R6A2S2R6S1G8S4G1R8A2A2A2A2S8S0S1S1S1RbZd0A2S4Z50R9A2A2M9G1A2R6A2S2R6S1G9Z10A2A2A2A2A2A2SeRdRcRaR9R8R7A6SaF_;F_;F_;F_;F_;F_;F_;Fz;Fmu;Fnf;Fc;Ftop;FT;FSB;").
Proof.
  intros SB T top c nf mu z HG Hc Hnf Hnf4 Hmu Hz HE. pose proof HG as (S1 & S2 & TG & T1 & T2 & ST & TB).
  pose proof (Sh_band (SB + c * 2 ^ 32) ltac:(lia)) as B1. pose proof (Sh_band (SB + c * 2 ^ 32 + mu) ltac:(lia)) as B3.
  pose proof (Sh_band (SB + c * 2 ^ 32 + 2 ^ 32) ltac:(lia)) as B4.
  unfold envR in HE.
  destruct Hz as [Hz|[Hz|[Hz|Hz]]]; destruct HE as [H|[H|[H|[H|[H|H]]]]]; lia.
Qed.

Lemma envR_dec : ltac2:(tb__ "0|1|
S7S7S7S7S7S7S9SeR6R5R4R3R2R1A6M0SbG0A1A2Fz;Fmu;Fnf;Fc;FT;FSB;").
Proof. intros. unfold envR. lia. Qed.
