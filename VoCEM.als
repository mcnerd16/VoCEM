//cipher objects
sig PrivKey { }
sig EncKey { createEK : one PrivKey }
sig SignKey {  createSK : one PrivKey }
sig Message { dec: EncKey one -> one Ciphertext }
sig Ciphertext { enc: EncKey one -> one Message, verifying : SignKey one -> one Signature }
sig Signature { signing : SignKey one -> one Ciphertext }
//Encryption Standards
pred EncryptionValid{
	all m:Message,k:EncKey | lone c:Ciphertext | enc.m.k = c
	all c:Ciphertext,k:EncKey | lone m:Message | dec.c.k = m
	all m:Message,k:EncKey | dec.(enc.m.k).k = m
	all c:Ciphertext,k:EncKey | enc.(dec.c.k).k = c
}
//Signature Standards
pred SigningValid{
	all c:Ciphertext, k:SignKey | lone s:Signature | signing.c.k = s
	all s:Signature, k:SignKey | lone c:Ciphertext | verifying.s.k = c
	all c:Ciphertext, k:SignKey | verifying.(signing.c.k).k = c
}
//Key Generation Facts (pred creates counterExample)
fact KeyGen {
	all pk:PrivKey | lone ek:EncKey | createEK.pk = ek
	all pk:PrivKey | lone sk:SignKey | createSK.pk = sk
	all pk1,pk2:PrivKey | createEK.pk1 = createEK.pk2 => createSK.pk1 != createSK.pk2 //Strongest Assumptions
	all pk1,pk2:PrivKey | createSK.pk1 = createSK.pk2 => createEK.pk1 != createEK.pk2 //Strongest Assumptions
}
//Checks if encryption is valid
MessCiphOK: check {
	all m1,m2:Message,k:EncKey | m1 != m2 => enc.m1.k != enc.m2.k //no repeated ciphertext per message
	all m:Message,k1,k2:EncKey | k1 != k2 => enc.m.k1 != enc.m.k2 //not repeated ciphertext per key
	all c1,c2:Ciphertext,k:EncKey | c1 != c2 => dec.c1.k != dec.c2.k //no repeated message per ciphertext
	all c:Ciphertext,k1,k2:EncKey | k1 != k2 => dec.c.k1 != dec.c.k2 //not repeated message per key
}
//Checks if signing is valid
CiphSignOK: check {
	all c1,c2:Ciphertext,k:SignKey | c1 != c2 => signing.c1.k != signing.c2.k //no repeated signature per ciphertext
	all c:Ciphertext,k1,k2:SignKey | k1 != k2 => signing.c.k1 != signing.c.k2 //no repeated signature per key
	all s1,s2:Signature,k:SignKey | s1 != s2 => verifying.s1.k != verifying.s2.k //no repeated ciphertext per signature
	all s:Signature,k1,k2:SignKey | k1 != k2 => verifying.s.k1 != verifying.s.k2 //no repeated ciphertext per key
}
//Encrypt then MAC Standards with Key Generation
pred EncThenMAC {
	all pk:PrivKey,m:Message | lone c:Ciphertext | enc.m.(createEK.pk) = c
	all pk:PrivKey,c:Ciphertext | lone m:Message | dec.c.(createEK.pk) = m
	all m:Message,pk:PrivKey | dec.(enc.m.(createEK.pk)).(createEK.pk) = m
	all pk:PrivKey,c:Ciphertext  | lone s:Signature | signing.c.(createSK.pk) = s
	all pk:PrivKey,s:Signature| lone c:Ciphertext | verifying.s.(createSK.pk) = c
	all c:Ciphertext,pk:PrivKey | verifying.(signing.c.(createSK.pk)).(createSK.pk) = c
}
//Checks if Encrypt-then-MAC is valid repeating test for encryption and signing
EncMacOK : check {
	all m1,m2:Message,k:PrivKey | m1 != m2 => enc.m1.(createEK.k) != enc.m2.(createEK.k)
	all m:Message,k1,k2:PrivKey | k1 != k2 => enc.m.(createEK.k1) != enc.m.(createEK.k2)
	all c1,c2:Ciphertext,k:PrivKey | c1 != c2 => dec.c1.(createEK.k) != dec.c2.(createEK.k)
	all c:Ciphertext,k1,k2:PrivKey | k1 != k2 => dec.c.(createEK.k1) != dec.c.(createEK.k2)
	all c1,c2:Ciphertext,k:PrivKey | c1 != c2 => signing.c1.(createSK.k) != signing.c2.(createSK.k)
	all c:Ciphertext,k1,k2:PrivKey | k1 != k2 => signing.c.(createSK.k1) != signing.c.(createSK.k2)
	all s1,s2:Signature,k:PrivKey | s1 != s2 => verifying.s1.(createSK.k) != verifying.s2.(createSK.k)
	all s:Signature,k1,k2:PrivKey | k1 != k2 => verifying.s.(createSK.k1) != verifying.s.(createSK.k2)
}

pred attack [ek:EncKey,sk:SignKey] {
	all m:Message,c:Ciphertext | enc.m.ek = c <=> dec.c.ek = m
	all c:Ciphertext,s:Signature | signing.c.sk = s <=> verifying.s.sk = c
}

run attack
