#include <stdio.h>

int main(){
	int a[10];
	int limit = 10;
	int st = -1, j;

	while (st < limit){
		st++;
		limit --;
		for (j = st; j < limit; j++){
			if (a[j] == a[j+1]) {
			}
		}
	}
	printf("Try illegal access %d\n",a[11]);
	return 0;
}
