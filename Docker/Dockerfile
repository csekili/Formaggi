FROM eparker05/blender:2.78c

WORKDIR /usr/src/app

COPY . .

RUN apt-get update && apt-get install -y --no-install-recommends apt-utils && \
	apt-get install -y build-essential checkinstall && \
	apt-get install -y libreadline-gplv2-dev libncursesw5-dev libssl-dev libsqlite3-dev tk-dev libgdbm-dev libc6-dev libbz2-dev && \
	echo $PWD/image_generation >> /usr/local/blender/2.78/python/lib/python3.5/site-packages/clevr.pth && \
	cd /usr/src && \
	apt-get install -y wget && \
	wget https://www.python.org/ftp/python/3.5.6/Python-3.5.6.tgz && \
	tar xzf Python-3.5.6.tgz && \
	cd Python-3.5.6 && \
	./configure --enable-optimizations && \
	make install && \
	apt-get install -y python3-pip
	

